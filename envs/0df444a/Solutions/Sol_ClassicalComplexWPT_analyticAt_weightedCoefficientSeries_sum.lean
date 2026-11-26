-- Prove2me | solution 1 for ClassicalComplexWPT.analyticAt_weightedCoefficientSeries_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:08:40.735086+00:00
-- url     : https://prove2.me/submissions/2eeedfcf-d8c1-471d-b815-84b5a54818b5

import Definitions.Def_ClassicalComplexWPT_AnalyticSeries
import Mathlib.Analysis.Normed.Lp.lpSpace
import Definitions.Def_ClassicalComplexWPT_WeightedCoefficientMap
import Theorems.Thm_ClassicalComplexWPT_radius_weightedCoefficientSeries_pos

set_option autoImplicit true
open scoped NNReal ENNReal Topology
open ClassicalComplexWPT
set_option maxHeartbeats 800000
namespace ClassicalComplexWPT
theorem _root_.solution {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) :
    AnalyticAt ℂ (weightedCoefficientSeries p r).sum 0 :=
  ((weightedCoefficientSeries p r).hasFPowerSeriesOnBall
    (radius_weightedCoefficientSeries_pos p r hr)).analyticAt
end ClassicalComplexWPT
