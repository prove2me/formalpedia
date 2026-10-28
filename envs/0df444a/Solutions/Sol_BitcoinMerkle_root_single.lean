-- Prove2me | solution 1 for BitcoinMerkle.root_single
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T04:36:59.489181+00:00
-- url     : https://prove2.me/submissions/6ec5738d-e250-4d6d-ab9b-aca0a5eef503

import Definitions.Def_BitcoinMerkle

open BitcoinMerkle

/-- Loop exit. -/
private theorem rootLoop_stop {H : Type} [DecidableEq H] (c : H → H → H) (z : H)
    (hs : List H) (m : Bool) (h : ¬ 1 < hs.length) :
    BitcoinMerkle.rootLoop c z hs m = (hs.headD z, m) := by
  rw [rootLoop, dif_neg h]

theorem solution {H : Type} [DecidableEq H] (c : H → H → H) (z : H) (a : H) :
    BitcoinMerkle.computeMerkleRoot c z [a] = (a, false) := by
  unfold computeMerkleRoot
  rw [rootLoop_stop c z [a] false (by simp)]
  rfl
