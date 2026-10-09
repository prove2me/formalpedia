-- Prove2me | solution 1 for BookProof.ChapterEulerGenericDensity.eulerVec_unit
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:48:16.190987+00:00
-- url     : https://prove2.me/submissions/5cc2433b-fb27-424b-9030-316e54ea235a

-- Generated from ChapterEulerGenericDensity.lean — solution of BookProof.ChapterEulerGenericDensity.eulerVec_unit
import Mathlib
import Definitions.Def_ChapterEulerGenericDensity
open BookProof.ChapterEulerGenericDensity



open scoped Matrix
open Matrix


variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (θ : ℝ) (l w : Fin d → ℝ)
    (hll : l ⬝ᵥ l = 1) (hww : w ⬝ᵥ w = 1) (hlw : l ⬝ᵥ w = 0) :
    eulerVec θ l w ⬝ᵥ eulerVec θ l w = 1 := by

  have hwl : w ⬝ᵥ l = 0 := by rw [dotProduct_comm]; exact hlw
  simp only [eulerVec, dotProduct_add, add_dotProduct, dotProduct_smul, smul_dotProduct,
    smul_eq_mul, hll, hww, hlw, hwl]
  nlinarith [Real.sin_sq_add_cos_sq θ]
