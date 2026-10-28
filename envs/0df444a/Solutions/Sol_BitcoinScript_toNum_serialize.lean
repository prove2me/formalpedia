-- Prove2me | solution 1 for BitcoinScript.toNum_serialize
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T05:50:52.552427+00:00
-- url     : https://prove2.me/submissions/9c2375c1-38a5-4667-817d-823a736a6e3e

import Definitions.Def_BitcoinScript
import Theorems.Thm_BitcoinScript_serialize_roundtrip
import Theorems.Thm_BitcoinScript_serialize_minimal

open BitcoinScript

theorem solution (n : Int) (h : (BitcoinScript.serialize n).length ≤ 4) :
    BitcoinScript.toNum true 4 (BitcoinScript.serialize n) = some n := by
  unfold toNum
  rw [if_neg (by omega), BitcoinScript.serialize_minimal]
  simp [BitcoinScript.serialize_roundtrip]
