-- Prove2me | solution 1 for BitcoinTaproot.opsuccess_accepts
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T16:39:26.109952+00:00
-- url     : https://prove2.me/submissions/6b095fc6-3d82-4240-8401-7a2c96ad11fb

import Definitions.Def_BitcoinTaproot
open BitcoinTaproot BitcoinSer BitcoinSig BitcoinVerify
open BitcoinScript hiding Bytes Byte

theorem solution (c : TapCtx) (ed : ExecData) (stack : List Bytes) (script : Bytes) (weight : Int)
    (h : BitcoinTaproot.opSuccessScan script.length script = some true) :
    BitcoinTaproot.executeTapscript c ed stack script weight = true := by
  unfold executeTapscript; rw [h]
