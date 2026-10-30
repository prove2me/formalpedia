-- Prove2me | solution 1 for BitcoinScriptV2.legacyOracle_eq
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-30T00:28:33.608473+00:00
-- url     : https://prove2.me/submissions/9730d8e8-9a8c-4389-b894-82b3e6628b63

import Definitions.Def_BitcoinScriptV2

open BitcoinScriptV2 BitcoinScript BitcoinSig BitcoinVerify

set_option linter.unusedSimpArgs false

theorem solution (f : BitcoinSig.SigFlags) (tx : BitcoinSer.Tx) (nIn : Nat) (amount : Int)
    (v : BitcoinSig.SigVersion) (sc : BitcoinScript.Bytes) :
    BitcoinSig.legacyOracle f tx nIn amount v sc =
      BitcoinScriptV2.withCodeSig (BitcoinScriptV2.legacyOracleV2 f tx nIn amount v) v sc := by
  rfl
