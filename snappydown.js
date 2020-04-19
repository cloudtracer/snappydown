var inherits = require('inherits')
var AbstractLevelDOWN = require('abstract-leveldown').AbstractLevelDOWN
var AbstractIterator = require('abstract-leveldown').AbstractIterator
var ltgt = require('ltgt')
var createRBT = require('functional-red-black-tree')
var Buffer = require('safe-buffer').Buffer
var path = require('path')
var fs = require('fs')
const mkdirp = require('mkdirp')
const writeFileAtomic = require('write-file-atomic')
var snappyjs = require('snappyjs')

var isDebug = false

// In Node, use global.setImmediate. In the browser, use a consistent
// microtask library to give consistent microtask experience to all browsers
var setImmediate = global.setImmediate
var NONE = {}

// TODO (perf): replace ltgt.compare with a simpler, buffer-only comparator
function gt (value) {
  return ltgt.compare(value, this._upperBound) > 0
}

function gte (value) {
  return ltgt.compare(value, this._upperBound) >= 0
}

function lt (value) {
  return ltgt.compare(value, this._upperBound) < 0
}

function lte (value) {
  return ltgt.compare(value, this._upperBound) <= 0
}

function SnappyIterator (db, options) {
  if (isDebug) console.error(db)
  if (isDebug) console.error(options)
  AbstractIterator.call(this, db)
  this._limit = options.limit
  if (this._limit === -1) this._limit = Infinity

  var tree = db._store
  this.location = db.location
  this.keyAsBuffer = options.keyAsBuffer !== false
  this.valueAsBuffer = options.valueAsBuffer !== false
  this._reverse = options.reverse
  this._options = options
  this._done = 0

  if (!this._reverse) {
    this._incr = 'next'
    this._lowerBound = ltgt.lowerBound(options, NONE)
    this._upperBound = ltgt.upperBound(options, NONE)

    if (this._lowerBound === NONE) {
      this._tree = tree.begin
    } else if (ltgt.lowerBoundInclusive(options)) {
      this._tree = tree.ge(this._lowerBound)
    } else {
      this._tree = tree.gt(this._lowerBound)
    }

    if (this._upperBound !== NONE) {
      if (ltgt.upperBoundInclusive(options)) {
        this._test = lte
      } else {
        this._test = lt
      }
    }
  } else {
    this._incr = 'prev'
    this._lowerBound = ltgt.upperBound(options, NONE)
    this._upperBound = ltgt.lowerBound(options, NONE)

    if (this._lowerBound === NONE) {
      this._tree = tree.end
    } else if (ltgt.upperBoundInclusive(options)) {
      this._tree = tree.le(this._lowerBound)
    } else {
      this._tree = tree.lt(this._lowerBound)
    }

    if (this._upperBound !== NONE) {
      if (ltgt.lowerBoundInclusive(options)) {
        this._test = gte
      } else {
        this._test = gt
      }
    }
  }
}

inherits(SnappyIterator, AbstractIterator)

function decode (value, asBuffer) {
  if (asBuffer) {
    return value
  } else {
    return value.toString()
  }
}

function encode (value, isValue) {
  if (isValue && !value) {
    value = Buffer.from('')
  }
  if (!Buffer.isBuffer(value) && typeof value !== 'string') {
    value = String(value)
  }
  if (!Buffer.isBuffer(value)) {
    value = Buffer.from(value)
  }
  return value
}

function doEncode (value, isValue) {
  var out = encode(value, isValue)
  return out.toString(isValue ? 'base64' : 'hex')
}

function doDecode (value, asBuffer, isValue) {
  return decode(Buffer.from(value, isValue ? 'base64' : 'hex'), asBuffer)
}
SnappyIterator.prototype._next = function (callback) {
  if (isDebug) console.error('_next called')

  this.db.fetchAllKeys()
  var key
  var value

  if (this._done++ >= this._limit) return setImmediate(callback)
  if (!this._tree.valid) return setImmediate(callback)

  key = this._tree.key
  value = this._tree.value

  if (!this._test(key)) return setImmediate(callback)
  var fileKey = this._fileKey(key)
  if (!this.keyAsBuffer) {
    key = key.toString()
  }
  if (fileKey) {
    try {
      ReadFilePromise(fileKey, {}).then(function (value) {
        if (this.valueAsBuffer) {
          value = value.toString()
        }
        this._tree[this._incr]()

        setImmediate(function callNext () {
          callback(null, key, value)
        })
      }.bind(this))
    } catch (err) {
      console.error(err)
      if (this.valueAsBuffer) {
        value = value.toString()
      }
      this._tree[this._incr]()

      setImmediate(function callNext () {
        callback(null, key, value)
      })
    }
  } else {
    if (this.valueAsBuffer) {
      value = value.toString()
    }
    this._tree[this._incr]()

    setImmediate(function callNext () {
      callback(null, key, value)
    })
  }
}

SnappyIterator.prototype._test = function () {
  return true
}

SnappyIterator.prototype._outOfRange = function (target) {
  if (!this._test(target)) {
    return true
  } else if (this._lowerBound === NONE) {
    return false
  } else if (!this._reverse) {
    if (ltgt.lowerBoundInclusive(this._options)) {
      return ltgt.compare(target, this._lowerBound) < 0
    } else {
      return ltgt.compare(target, this._lowerBound) <= 0
    }
  } else {
    if (ltgt.upperBoundInclusive(this._options)) {
      return ltgt.compare(target, this._lowerBound) > 0
    } else {
      return ltgt.compare(target, this._lowerBound) >= 0
    }
  }
}

SnappyIterator.prototype._seek = function (target) {
  if (isDebug) console.error('_seek called')

  if (target.length === 0) {
    throw new Error('cannot seek() to an empty target')
  }

  if (this._outOfRange(target)) {
    this._tree = this.db._store.end
    this._tree.next()
  } else if (this._reverse) {
    this._tree = this.db._store.le(target)
  } else {
    this._tree = this.db._store.ge(target)
  }
}

SnappyIterator.prototype._fileKey = function (key) {
  key = doEncode(key)
  if (isDebug) console.error(key)
  return path.join(this.location, key + '.mbz')
}
function SnappyDown (options) {
  if (!(this instanceof SnappyDown)) {
    return new SnappyDown(options)
  }
  var cwdPath = process.cwd()
  if (isDebug) console.error('Options: ' + typeof options)
  if (isDebug) console.error(options)
  if (isDebug) console.error('Path is: ' + typeof cwdPath + ' - ' + cwdPath)
  if (options) options.path = cwdPath
  AbstractLevelDOWN.call({
    keysLoaded: true,
    bufferKeys: true,
    snapshots: true,
    permanence: true,
    seek: true,
    clear: true
  }, options)

  this._store = createRBT(ltgt.compare)
  this.status = 'unknown'
  this.supports = {}
  this.supports.additionalMethods = {
    keysLoaded: true,
    bufferKeys: true,
    snapshots: true,
    permanence: true,
    seek: true,
    clear: true
  }
}

inherits(SnappyDown, AbstractLevelDOWN)

function _translateHexToAscii (h) {
  return doDecode(Buffer.from(h, 'hex'), true, false)
}

SnappyDown.prototype._open = function (options, callback) {
  if (isDebug) console.error('_open called:')
  if (isDebug) console.error(options)
  var cwdPath = process.cwd()
  options.path = cwdPath
  var self = this
  if (options.name) {
    this.location = path.join(cwdPath, options.name)
    if (isDebug) console.error(this.location + ' is set')
  }
  this.location = path.join(cwdPath, 'in_memory')
  if (options && options.location) {
    this.location = path.join(cwdPath, options.location)
  }
  if (options.name) {
    this.location = path.join(cwdPath, options.name)
  }
  this.path = this.location
  mkdirp.sync(this.location)
  setImmediate(function callNext () {
    if (isDebug) console.error('callnext')
    self.fetchAllKeys()
    if (isDebug) console.error(self)
    callback(null, self)
  })
}
var counter = 0
SnappyDown.prototype.fetchAllKeys = function () {
  if (isDebug) console.error('fetchAllKeys called')

  if (!this.keysLoaded) {
    this.keysLoaded = true
    var files = fs.readdirSync(this.location)
    var newStore = createRBT(ltgt.compare)
    if (isDebug) console.error('FullPath is: ' + typeof cwdPath + ' - ' + this.location)

    for (var i = 0, l = files.length; i < l; i++) {
      var file = files[i]
      if (isDebug) console.error(file)
      newStore = newStore.insert(_translateHexToAscii(file.replace('.mbz', '')), 'true')
    }
    this._store = newStore
    counter++
    if (isDebug) console.error('Counter called: ' + counter)
  }
}
SnappyDown.prototype._serializeKey = function (key) {
  return Buffer.isBuffer(key) ? key : Buffer.from(String(key))
}

SnappyDown.prototype._serializeValue = function (value) {
  return Buffer.isBuffer(value) ? value : Buffer.from(String(value))
}

SnappyDown.prototype._fileKey = function (key) {
  key = doEncode(key)
  if (isDebug) console.error(key)
  return path.join(this.location, key + '.mbz')
}

function nextdir (dir) {
  dir = dir.split(path.sep)
  dir.pop()
  return dir.join(path.sep)
}

function cleandir (dir, location, cb) {
  if (!dir) return cb(null)
  if (dir === location) return cb(null)

  fs.rmdir(dir, (err) => {
    if (err && err.code !== 'ENOTEMPTY') return cb(err)
    else if (err) return cb(null)
    cleandir(nextdir(dir), location, cb)
  })
}

cleandir.sync = function (dir, location) {
  if (!dir) return
  if (dir === location) return

  try {
    fs.rmdirSync(dir)
  } catch (err) {
    if (err.code !== 'ENOTEMPTY') if (isDebug) console.error(err)
  }
  cleandir.sync(nextdir(dir), location)
}

SnappyDown.prototype._put = function (key, value, options, callback) {
  var iter = this._store.find(key)
  var fileKey = this._fileKey(key)
  if (isDebug) console.error('_put: ' + fileKey + ' : ' + value)
  if (iter.valid) {
    this._store = iter.update(1)
  } else {
    if (typeof value === 'undefined') {
      this._store = this._store.insert(key, value)
    } else {
      this._store = this._store.insert(key, 1)
    }
  }
  value = CompressData(value)
  writeFileAtomic(fileKey, value, options, function () {
    setImmediate(callback)
  })
}

SnappyDown.prototype._get = function (key, options, callback) {
  var fileKey = this._fileKey(key)
  if (isDebug) console.error('_get: ' + key + ' - ' + fileKey)
  var value = this._store.get(key)
  if (isDebug) console.error(value)
  try {
    ReadFilePromise(fileKey, options).then(function (value) {
      if (typeof value === 'undefined') {
        return setImmediate(function callNext () {
          callback(new Error('NotFound'))
        })
      }
      setImmediate(function callNext () {
        callback(null, value)
      })
    })
  } catch (err) {
    value = undefined
    if (isDebug) console.error(err)
  }
}

SnappyDown.prototype._del = function (key, options, callback) {
  var fileKey = this._fileKey(key)
  if (isDebug) console.error('_del : ' + fileKey)
  this._store = this._store.remove(key)
  fs.unlink(fileKey, function () {
    setImmediate(callback)
  })
}

function CompressData (data) {
  if (!data) return data
  data = encode(data, true)
  return snappyjs.compress(data)
}

function DecompressData (data) {
  try {
    if (!data) return data
    return snappyjs.uncompress(data)
  } catch (err) {
    console.error(err)
    return data
  }
}

function WriteFilePromise (fileKey, value, options) {
  value = CompressData(value)
  return new Promise(function (resolve, reject) {
    writeFileAtomic(fileKey, value, options, function () {
      resolve(true)
    })
  })
}

function DeleteFilePromise (fileKey) {
  return new Promise(function (resolve, reject) {
    fs.unlink(fileKey, function () {
      resolve(true)
    })
  })
}

function ReadFilePromise (fileKey, options) {
  return new Promise(function (resolve, reject) {
    try {
      fs.readFile(fileKey, function (err, value) {
        if (err) {
          console.error(err)
        }
        if (typeof value === 'undefined') {
          return resolve(value)
        }
        value = DecompressData(value)
        if (isDebug) console.error('After Read: ' + typeof value + ' - ' + value)
        if (!options.asBuffer) {
          value = value.toString()
          if (isDebug) console.error(value)
        }
        return resolve(value)
      })
    } catch (error) {
      console.error(error)
      resolve(undefined)
    }
  })
}

SnappyDown.prototype._batch = function (array, options, callback) {
  var i = -1
  var key
  var value
  var iter
  var len = array.length
  var tree = this._store
  var promises = []

  while (++i < len) {
    key = array[i].key
    iter = tree.find(key)
    var fileKey = this._fileKey(key)
    if (array[i].type === 'put') {
      value = array[i].value
      tree = iter.valid ? iter.update(1) : tree.insert(key, 1)
      if (isDebug) console.error('_batch put: ' + fileKey + ' : ' + value)
      promises.push(WriteFilePromise(fileKey, value, options))
    } else {
      tree = iter.remove()
      try {
        if (isDebug) console.error('_batch remove: ' + fileKey)
        promises.push(DeleteFilePromise(fileKey))
      } catch (err) {
        if (isDebug) console.error(err)
      }
    }
  }
  this._store = tree
  Promise.all(promises).then(function (stuffThatDoesntMatter) {
    setImmediate(callback)
  })
}

SnappyDown.prototype._iterator = function (options) {
  return new SnappyIterator(this, options)
}

module.exports = SnappyDown.default = SnappyDown
// Exposed for unit tests only
module.exports.SnappyIterator = SnappyIterator
