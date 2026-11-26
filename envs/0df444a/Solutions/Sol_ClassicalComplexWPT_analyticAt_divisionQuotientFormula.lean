-- Prove2me | solution 1 for ClassicalComplexWPT.analyticAt_divisionQuotientFormula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:16:47.367983+00:00
-- url     : https://prove2.me/submissions/38614588-0a46-4bc9-bd60-bb615a37fe5f

import Definitions.Def_ClassicalComplexWPT_WeightedSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Constructions
import Definitions.Def_ClassicalComplexWPT_L1Division
import Theorems.Thm_ClassicalComplexWPT_analyticAt_inverseOneAdd_apply

set_option autoImplicit true
open Finset
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT
variable {A : Type*} [AddCommMonoid A] [Finset.HasAntidiagonal A]
namespace ClassicalComplexWPT
theorem _root_.solution (d : ℕ)
    (pf : L1Coeff (A × ℕ) × L1Coeff (A × ℕ)) (hp : ‖pf.1‖ < 1) :
    AnalyticAt ℂ (fun x ↦ Ring.inverse (1 + divisionOperatorInput d x)
      (divisionRhsInput d x)) pf := by
  have hK : ‖divisionOperatorInput (A := A) d pf‖ < 1 :=
    lt_of_le_of_lt (norm_divisionPerturbation_le d pf.1) hp
  exact analyticAt_inverseOneAdd_apply
    (divisionOperatorInput (A := A) d) (divisionRhsInput (A := A) d) pf hK
end ClassicalComplexWPT
