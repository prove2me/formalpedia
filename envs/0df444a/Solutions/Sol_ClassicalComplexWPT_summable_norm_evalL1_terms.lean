-- Prove2me | solution 1 for ClassicalComplexWPT.summable_norm_evalL1_terms
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:58:16.22981+00:00
-- url     : https://prove2.me/submissions/ea84c23f-aa81-482b-b83f-11d3bd670bbc

import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Data.Finsupp.Antidiagonal
import Mathlib.Data.Finsupp.Weight
import Definitions.Def_ClassicalComplexWPT_WeightedSeries
import Theorems.Thm_ClassicalComplexWPT_norm_monomial_le_one

set_option autoImplicit true
open Finset
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT
variable {S : Type*}
namespace ClassicalComplexWPT
theorem _root_.solution (f : L1Coeff (S →₀ ℕ)) (y : S → ℂ)
    (hy : ∀ i, ‖y i‖ ≤ 1) :
    Summable (fun a ↦ ‖f a * monomial y a‖) := by
  refine (L1Coeff.summable_norm f).of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun a ↦ ?_)
  calc
    ‖f a * monomial y a‖ ≤ ‖f a‖ * ‖monomial y a‖ := norm_mul_le _ _
    _ ≤ ‖f a‖ * 1 :=
      mul_le_mul_of_nonneg_left (norm_monomial_le_one y hy a) (norm_nonneg _)
    _ = ‖f a‖ := mul_one _
end ClassicalComplexWPT
