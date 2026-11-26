-- Prove2me | solution 1 for ClassicalComplexWPT.analyticAt_preparationUnit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:14:02.435904+00:00
-- url     : https://prove2.me/submissions/891bb54b-9d31-4dd1-8b12-5a626cb254d1

import Definitions.Def_ClassicalComplexWPT_PreparationSequences
import Definitions.Def_ClassicalComplexWPT_WeightedEvaluation
import Definitions.Def_ClassicalComplexWPT_L1PolynomialEvaluation
import Definitions.Def_ClassicalComplexWPT_WeightedGermEvaluation
import Definitions.Def_ClassicalComplexWPT_PublicExistence
import Theorems.Thm_ClassicalComplexWPT_analyticAt_preparationQuotientEval
import Theorems.Thm_ClassicalComplexWPT_preparationQuotientEval_zero

set_option autoImplicit true
open Filter
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
set_option maxHeartbeats 1000000
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) (d : ℕ)
    (hq : AnalyticAt ℂ (normalizedPreparationQuotient p r hr d) 0)
    (hq0 : normalizedPreparationQuotient p r hr d 0 0 = 1) :
    AnalyticAt ℂ (preparationUnit p r hr d) 0 := by
  have hQ := analyticAt_preparationQuotientEval p r hr d hq
  have hQ0 : preparationQuotientEval p r hr d 0 ≠ 0 := by
    rw [preparationQuotientEval_zero, hq0]
    exact one_ne_zero
  exact analyticAt_const.mul (hQ.inv hQ0)
end ClassicalComplexWPT
