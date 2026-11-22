-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.norm_gramSchmidt_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:30:14.458334+00:00
-- url     : https://prove2.me/submissions/bae9467a-37e3-403d-b96a-d4578a51a842

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SchurAverage

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open InnerProductSpace
variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℂ U]
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {r : ℕ} (a : Fin r → U) (n : Fin r) : ‖gramSchmidt ℂ a n‖ ≤ ‖a n‖ := by
  have h1 : inner ℂ (gramSchmidt ℂ a n) (a n) = ((‖gramSchmidt ℂ a n‖ ^ 2 : ℝ) : ℂ) := by
    have h0 := gramSchmidt_def'' ℂ a n
    have h2 : inner ℂ (gramSchmidt ℂ a n) (a n) = inner ℂ (gramSchmidt ℂ a n) _ :=
      congrArg (inner ℂ (gramSchmidt ℂ a n)) h0
    rw [h2, inner_add_right, inner_sum, Finset.sum_eq_zero, add_zero, inner_self_eq_norm_sq_to_K]
    · push_cast; rfl
    · intro i hi
      rw [inner_smul_right, gramSchmidt_orthogonal ℂ a (Finset.mem_Iio.1 hi).ne', mul_zero]
  have h2 : ‖gramSchmidt ℂ a n‖ ^ 2 ≤ ‖gramSchmidt ℂ a n‖ * ‖a n‖ := by
    have := norm_inner_le_norm (𝕜 := ℂ) (gramSchmidt ℂ a n) (a n)
    rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at this
    exact this
  by_cases h0 : ‖gramSchmidt ℂ a n‖ = 0
  · rw [h0]; positivity
  · have : 0 < ‖gramSchmidt ℂ a n‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    nlinarith
end Formalism.HermitianLatticeCounting.P
