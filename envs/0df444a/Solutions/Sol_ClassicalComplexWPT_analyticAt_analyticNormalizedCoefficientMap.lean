-- Prove2me | solution 1 for ClassicalComplexWPT.analyticAt_analyticNormalizedCoefficientMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:09:28.050029+00:00
-- url     : https://prove2.me/submissions/c69eba3d-2e2e-45e8-b980-c0a3ee2773ad

import Definitions.Def_ClassicalComplexWPT_AnalyticSeries
import Definitions.Def_ClassicalComplexWPT_ExactOrder
import Definitions.Def_ClassicalComplexWPT_WeightedSeries
import Definitions.Def_ClassicalComplexWPT_WeightedCoefficientMap
import Definitions.Def_ClassicalComplexWPT_NormalizedCoefficients
import Theorems.Thm_ClassicalComplexWPT_analyticAt_normalizedCoefficientMap
import Theorems.Thm_ClassicalComplexWPT_analyticAt_weightedCoefficientSeries_sum


set_option autoImplicit true
open Filter
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
set_option maxHeartbeats 1000000
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) (d : ℕ) :
    AnalyticAt ℂ (analyticNormalizedCoefficientMap p r hr d) 0 := by
  exact analyticAt_normalizedCoefficientMap _ _
    (analyticAt_weightedCoefficientSeries_sum p r hr)
end ClassicalComplexWPT
