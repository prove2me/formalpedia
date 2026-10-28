-- Prove2me | solution 1 for BitcoinMerkle.root_pair
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T04:37:00.192522+00:00
-- url     : https://prove2.me/submissions/6272926e-32a0-4019-b7b5-13b288c53f4e

import Definitions.Def_BitcoinMerkle

open BitcoinMerkle

/-- One iteration of the loop. -/
private theorem rootLoop_step {H : Type} [DecidableEq H] (c : H → H → H) (z : H)
    (hs : List H) (m : Bool) (h : 1 < hs.length) :
    BitcoinMerkle.rootLoop c z hs m = BitcoinMerkle.rootLoop c z (BitcoinMerkle.pairUp c hs) (m || BitcoinMerkle.hasEqualPair hs) := by
  conv => lhs; rw [rootLoop]
  rw [dif_pos h]

/-- Loop exit. -/
private theorem rootLoop_stop {H : Type} [DecidableEq H] (c : H → H → H) (z : H)
    (hs : List H) (m : Bool) (h : ¬ 1 < hs.length) :
    BitcoinMerkle.rootLoop c z hs m = (hs.headD z, m) := by
  rw [rootLoop, dif_neg h]

theorem solution {H : Type} [DecidableEq H] (c : H → H → H) (z : H) (a b : H) :
    BitcoinMerkle.computeMerkleRoot c z [a, b] = (c a b, decide (a = b)) := by
  unfold computeMerkleRoot
  rw [rootLoop_step c z [a, b] false (by simp)]
  simp only [pairUp, hasEqualPair, Bool.false_or, Bool.or_false]
  rw [rootLoop_stop c z [c a b] _ (by simp)]
  rfl
