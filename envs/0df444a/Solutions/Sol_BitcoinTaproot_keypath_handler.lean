-- Prove2me | solution 1 for BitcoinTaproot.keypath_handler
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T16:41:40.402995+00:00
-- url     : https://prove2.me/submissions/52f554f2-7a02-417b-a7b4-0f27a547d0cb

import Definitions.Def_BitcoinTaproot
open BitcoinTaproot BitcoinSer BitcoinSig BitcoinVerify
open BitcoinScript hiding Bytes Byte

theorem solution (spent : List TxOut) (c : BitcoinVerify.Ctx) (sig q : Bytes) :
    BitcoinTaproot.taprootHandler spent c [sig] q =
      BitcoinTaproot.checkSchnorrSignature c.tx spent c.nIn sig q false ⟨false, [], [], 0xFFFFFFFF⟩ := by
  simp [taprootHandler, hasAnnex]
