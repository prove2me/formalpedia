-- Prove2me | solution 1 for ClassicalComplexWPT.monomialWeight_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:14:56.288888+00:00
-- url     : https://prove2.me/submissions/eabb0420-2cba-4cc4-b3c0-d0a2e2a1ba27

import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Data.Finsupp.Antidiagonal
import Mathlib.Data.Finsupp.Weight
import Definitions.Def_ClassicalComplexWPT_WeightedSeries

set_option autoImplicit true
open Finset
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT
variable {S : Type*}
namespace ClassicalComplexWPT
theorem _root_.solution (r : S → ℝ) (a b : S →₀ ℕ) :
    monomialWeight r (a + b) = monomialWeight r a * monomialWeight r b := by
  classical
  exact Finsupp.prod_add_index' (fun _ ↦ pow_zero _) (fun _ m n ↦ pow_add _ m n)
end ClassicalComplexWPT
