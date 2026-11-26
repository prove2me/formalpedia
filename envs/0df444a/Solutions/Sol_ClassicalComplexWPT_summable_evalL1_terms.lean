-- Prove2me | solution 1 for ClassicalComplexWPT.summable_evalL1_terms
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:15:32.953868+00:00
-- url     : https://prove2.me/submissions/0676b04e-ab65-46d1-914b-70ba0b21ca39

import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Data.Finsupp.Antidiagonal
import Mathlib.Data.Finsupp.Weight
import Definitions.Def_ClassicalComplexWPT_WeightedSeries
import Theorems.Thm_ClassicalComplexWPT_summable_norm_evalL1_terms

set_option autoImplicit true
open Finset
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT
variable {S : Type*}
namespace ClassicalComplexWPT
theorem _root_.solution (f : L1Coeff (S →₀ ℕ)) (y : S → ℂ)
    (hy : ∀ i, ‖y i‖ ≤ 1) :
    Summable (fun a ↦ f a * monomial y a) :=
  Summable.of_norm (summable_norm_evalL1_terms f y hy)
end ClassicalComplexWPT
