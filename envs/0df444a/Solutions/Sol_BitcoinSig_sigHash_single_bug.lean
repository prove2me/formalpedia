-- Prove2me | solution 1 for BitcoinSig.sigHash_single_bug
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T14:25:06.770045+00:00
-- url     : https://prove2.me/submissions/072014f6-2dbe-4d56-8d87-d4c59b26b0cc

import Definitions.Def_BitcoinSig

open BitcoinSig BitcoinSer in
theorem solution (scriptCode : Bytes) (tx : Tx) (nIn hashType : Nat)
    (h1 : hashType &&& 0x1f = BitcoinSig.SIGHASH_SINGLE) (h2 : tx.vout.length ≤ nIn) :
    BitcoinSig.sigHashLegacy scriptCode tx nIn hashType = BitcoinSig.uint256One := by
  simp [sigHashLegacy, h1, h2]
