-- Prove2me | solution 1 for BitcoinTaproot.keypath_annex
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T16:41:43.235131+00:00
-- url     : https://prove2.me/submissions/d6ff64dc-db26-4f8e-a92d-2484746f45ac

import Definitions.Def_BitcoinTaproot
open BitcoinTaproot BitcoinSer BitcoinSig BitcoinVerify
open BitcoinScript hiding Bytes Byte

theorem solution (spent : List TxOut) (c : BitcoinVerify.Ctx) (sig annex q : Bytes)
    (ha : (annex.getD 0 0).toNat = BitcoinTaproot.ANNEX_TAG) (hne : annex ≠ []) :
    BitcoinTaproot.taprootHandler spent c [sig, annex] q =
      BitcoinTaproot.checkSchnorrSignature c.tx spent c.nIn sig q false
        ⟨true, BitcoinSer.sha256 (BitcoinSer.serBytes annex), [], 0xFFFFFFFF⟩ := by
  obtain ⟨b, r, rfl⟩ : ∃ b r, annex = b :: r := by
    cases annex with
    | nil => exact absurd rfl hne
    | cons b r => exact ⟨b, r, rfl⟩
  have hb : b.toNat = ANNEX_TAG := by simpa using ha
  simp [taprootHandler, hasAnnex, hb]
