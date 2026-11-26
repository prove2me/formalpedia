-- Prove2me | solution 1 for ClassicalComplexWPT.norm_evalL1_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:15:36.991739+00:00
-- url     : https://prove2.me/submissions/2706eb5a-4577-471d-8541-f186ef792d01

import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Data.Finsupp.Antidiagonal
import Mathlib.Data.Finsupp.Weight
import Definitions.Def_ClassicalComplexWPT_WeightedSeries
import Theorems.Thm_ClassicalComplexWPT_monomial_zero
import Theorems.Thm_ClassicalComplexWPT_norm_monomial_le_one
import Theorems.Thm_ClassicalComplexWPT_summable_norm_evalL1_terms
attribute [local simp] ClassicalComplexWPT.monomial_zero

set_option autoImplicit true
open Finset
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT
variable {S : Type*}
namespace ClassicalComplexWPT
theorem _root_.solution (f : L1Coeff (S →₀ ℕ)) (y : S → ℂ)
    (hy : ∀ i, ‖y i‖ ≤ 1) : ‖evalL1 f y‖ ≤ ‖f‖ := by
  rw [L1Coeff.norm_eq_tsum_norm]
  exact (norm_tsum_le_tsum_norm (summable_norm_evalL1_terms f y hy)).trans <| by
    apply (summable_norm_evalL1_terms f y hy).tsum_le_tsum
    · intro a
      calc
        ‖f a * monomial y a‖ ≤ ‖f a‖ * ‖monomial y a‖ := norm_mul_le _ _
        _ ≤ ‖f a‖ := by
          simpa using
            mul_le_mul_of_nonneg_left (norm_monomial_le_one y hy a) (norm_nonneg (f a))
    · exact L1Coeff.summable_norm f
end ClassicalComplexWPT
