-- Prove2me | solution 1 for ClassicalComplexWPT.analyticAt_seqDivisionQuotientGlobal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:05:55.008014+00:00
-- url     : https://prove2.me/submissions/65cbee12-5c0d-4043-a45f-3090927639eb

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
namespace ClassicalComplexWPT
theorem _root_.solution (d : ℕ)
    (pf : L1Coeff ℕ × L1Coeff ℕ) (hp : ‖pf.1‖ < 1) :
    AnalyticAt ℂ (seqDivisionQuotientGlobal d) pf := by
  have hK : ‖seqDivisionOperatorInput d pf‖ < 1 :=
    lt_of_le_of_lt (norm_seqDivisionPerturbation_le d pf.1) hp
  exact analyticAt_inverseOneAdd_apply
    (seqDivisionOperatorInput d) (seqDivisionRhsInput d) pf hK
end ClassicalComplexWPT
