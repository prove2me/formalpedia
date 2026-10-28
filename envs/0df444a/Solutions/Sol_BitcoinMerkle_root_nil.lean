-- Prove2me | solution 1 for BitcoinMerkle.root_nil
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T04:36:58.838532+00:00
-- url     : https://prove2.me/submissions/e919da12-da3c-466c-8f81-b17c683d28c2

import Definitions.Def_BitcoinMerkle

open BitcoinMerkle

/-- Loop exit. -/
private theorem rootLoop_stop {H : Type} [DecidableEq H] (c : H → H → H) (z : H)
    (hs : List H) (m : Bool) (h : ¬ 1 < hs.length) :
    BitcoinMerkle.rootLoop c z hs m = (hs.headD z, m) := by
  rw [rootLoop, dif_neg h]

theorem solution {H : Type} [DecidableEq H] (c : H → H → H) (z : H) :
    BitcoinMerkle.computeMerkleRoot c z [] = (z, false) := by
  unfold computeMerkleRoot
  rw [rootLoop_stop c z [] false (by simp)]
  rfl
