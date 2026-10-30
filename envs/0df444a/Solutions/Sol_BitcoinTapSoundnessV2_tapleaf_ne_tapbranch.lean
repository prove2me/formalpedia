-- Prove2me | solution 1 for BitcoinTapSoundnessV2.tapleaf_ne_tapbranch
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-29T18:05:11.899386+00:00
-- url     : https://prove2.me/submissions/0f0ce211-19bf-4582-a4dc-b3b71458e4fc

import Definitions.Def_BitcoinTapSoundnessV2
import Theorems.Thm_BitcoinSer_sha256_length

open BitcoinTapSoundnessV2 BitcoinSer BitcoinTaproot

private theorem append_inj_len {α : Type} (a b c d : List α) (hl : a.length = c.length) (h : a ++ b = c ++ d) :
    a = c ∧ b = d :=
  List.append_inj h hl

/-- The `TapLeaf` and `TapBranch` tags hash differently. -/
theorem solution :
    BitcoinSer.sha256 (BitcoinSig.ascii "TapLeaf") ≠ BitcoinSer.sha256 (BitcoinSig.ascii "TapBranch") := by
  decide +kernel
