-- Prove2me | solution 1 for BookProof.ChapterRotaryPosition.norm_rotaryEncode
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T18:11:21.019331+00:00
-- url     : https://prove2.me/submissions/84de1e1f-8f9a-43f1-8787-5a0c6fa7bae9

-- Generated from ChapterRotaryPosition.lean — solution of BookProof.ChapterRotaryPosition.norm_rotaryEncode
import Mathlib
import Definitions.Def_ChapterRotaryPosition
import Definitions.Def_ChapterCoherentOverlapComplex
open BookProof.ChapterRotaryPosition



open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlapComplex

variable {n m : ℕ}

variable {n m : ℕ}


private theorem rotaryEncode_apply (omega : Fin n → ℝ) (p : ℝ) (q : EuclideanSpace ℂ (Fin n))
    (i : Fin n) :
    rotaryEncode omega p q i = Complex.exp ((p * omega i : ℝ) * Complex.I) * q i := rfl

set_option maxHeartbeats 1000000 in
theorem solution (omega : Fin n → ℝ) (p : ℝ) (q : EuclideanSpace ℂ (Fin n)) :
    ‖rotaryEncode omega p q‖ = ‖q‖ := by

  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [rotaryEncode_apply, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
