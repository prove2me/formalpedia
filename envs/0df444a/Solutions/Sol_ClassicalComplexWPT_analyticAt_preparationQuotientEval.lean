-- Prove2me | solution 1 for ClassicalComplexWPT.analyticAt_preparationQuotientEval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:12:19.273874+00:00
-- url     : https://prove2.me/submissions/fe80bb57-54f1-45b7-8cbe-99866b6fe09c

import Definitions.Def_ClassicalComplexWPT_PreparationSequences
import Definitions.Def_ClassicalComplexWPT_WeightedEvaluation
import Definitions.Def_ClassicalComplexWPT_L1PolynomialEvaluation
import Definitions.Def_ClassicalComplexWPT_WeightedGermEvaluation
import Definitions.Def_ClassicalComplexWPT_PublicExistence

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
    (hq : AnalyticAt ℂ (normalizedPreparationQuotient p r hr d) 0) :
    AnalyticAt ℂ (preparationQuotientEval p r hr d) 0 := by
  exact ClassicalComplexWPT.AnalyticAt.evalL1PowerSeries hq (r : ℂ)⁻¹
end ClassicalComplexWPT
