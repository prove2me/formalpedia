-- Prove2me | solution 1 for BookProof.ChapterTrajectory.midProb_sum
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:34:26.512714+00:00
-- url     : https://prove2.me/submissions/348b3c1c-f27b-4a41-aa93-af857ca748d8

-- Generated from ChapterTrajectory.lean — solution of BookProof.ChapterTrajectory.midProb_sum
import Mathlib
import Definitions.Def_ChapterTrajectory
open BookProof.ChapterTrajectory



open scoped BigOperators Matrix


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (U : Matrix (Fin n) (Fin n) ℂ) (psi : Fin n → ℂ)
    (hU : Uᴴ * U = 1) : ∑ a, midProb U psi a = ∑ a, ‖psi a‖ ^ 2 := by

  have h_unitary : ∀ (x : Fin n → ℂ), ∑ a, ‖(U *ᵥ x) a‖ ^ 2 = ∑ a, ‖x a‖ ^ 2 := by
    intro x
    have h_sum : ∑ a, (U *ᵥ x) a * starRingEnd ℂ ((U *ᵥ x) a)
        = ∑ a, x a * starRingEnd ℂ (x a) := by
      have h_step : ∑ a, (U *ᵥ x) a * starRingEnd ℂ ((U *ᵥ x) a)
          = ∑ a, (starRingEnd ℂ (x a)) * (Uᴴ *ᵥ (U *ᵥ x)) a := by
        simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.mul_sum, mul_comm,
          mul_assoc, Matrix.conjTranspose_apply, RCLike.star_def, mul_left_comm]
        exact Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ =>
          Finset.sum_congr rfl fun _ _ =>
            Finset.sum_congr rfl fun _ _ => by ring)
      simp_all [mul_comm]
    convert congr_arg Complex.re h_sum using 1 <;>
      norm_num [Complex.normSq, Complex.sq_norm]
  exact h_unitary psi
