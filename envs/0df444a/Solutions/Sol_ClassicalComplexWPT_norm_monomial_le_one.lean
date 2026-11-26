-- Prove2me | solution 1 for ClassicalComplexWPT.norm_monomial_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:57:28.325582+00:00
-- url     : https://prove2.me/submissions/78456cf3-db2d-4c81-a959-f9b3b78d5499

import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Data.Finsupp.Antidiagonal
import Mathlib.Data.Finsupp.Weight
import Definitions.Def_ClassicalComplexWPT_WeightedSeries
import Theorems.Thm_ClassicalComplexWPT_monomial_zero
attribute [local simp] ClassicalComplexWPT.monomial_zero

set_option autoImplicit true
open Finset
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT
variable {S : Type*}
namespace ClassicalComplexWPT
theorem _root_.solution (y : S → ℂ) (hy : ∀ i, ‖y i‖ ≤ 1) (a : S →₀ ℕ) :
    ‖monomial y a‖ ≤ 1 := by
  classical
  change ‖∏ i ∈ a.support, y i ^ a i‖ ≤ 1
  rw [norm_prod]
  simp only [norm_pow]
  apply Finset.prod_le_one
  · intro i hi
    exact pow_nonneg (norm_nonneg _) _
  · intro i hi
    exact pow_le_one₀ (norm_nonneg _) (hy i)
end ClassicalComplexWPT
