-- Prove2me | solution 1 for BookProof.MassGap.heisenberg_number_shift_invariant
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T16:39:44.4657+00:00
-- url     : https://prove2.me/submissions/3fa28421-cb51-4c3d-9315-dfee573198c3

-- Generated from ChapterMassGap.lean — solution of BookProof.MassGap.heisenberg_number_shift_invariant
import Mathlib
import Definitions.Def_ChapterMassGap
import Theorems.Thm_BookProof_MassGap_exp_conj_eq_self
open BookProof.MassGap


















open scoped BigOperators


variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸]

set_option maxHeartbeats 1000000 in
theorem solution (H N Obs : 𝔸) (t lam : ℂ)
    (hHN : Commute H N) (hON : Commute Obs N) :
    NormedSpace.exp (t • (H + lam • N)) * Obs * NormedSpace.exp (-(t • (H + lam • N)))
      = NormedSpace.exp (t • H) * Obs * NormedSpace.exp (-(t • H)) := by

  haveI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℂ 𝔸
  set X := t • H with hX
  set Y := t • (lam • N) with hY
  have hsplit : t • (H + lam • N) = X + Y := by rw [smul_add]
  have hXY : Commute X Y := ((hHN.smul_right lam).smul_left t).smul_right t
  have hObsY : Commute Obs Y := (hON.smul_right lam).smul_right t
  rw [hsplit, NormedSpace.exp_add_of_commute hXY]
  have hneg : -(X + Y) = -Y + -X := by abel
  rw [hneg, NormedSpace.exp_add_of_commute (hXY.symm.neg_left.neg_right)]
  calc NormedSpace.exp X * NormedSpace.exp Y * Obs
          * (NormedSpace.exp (-Y) * NormedSpace.exp (-X))
      = NormedSpace.exp X * (NormedSpace.exp Y * Obs * NormedSpace.exp (-Y))
          * NormedSpace.exp (-X) := by noncomm_ring
    _ = NormedSpace.exp X * Obs * NormedSpace.exp (-X) := by rw [exp_conj_eq_self hObsY]
