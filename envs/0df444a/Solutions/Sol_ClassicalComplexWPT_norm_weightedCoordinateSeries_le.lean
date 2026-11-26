-- Prove2me | solution 1 for ClassicalComplexWPT.norm_weightedCoordinateSeries_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:04:15.698616+00:00
-- url     : https://prove2.me/submissions/f9ecee19-857a-4c52-a413-64b696ee87f4

import Definitions.Def_ClassicalComplexWPT_AnalyticSeries
import Mathlib.Analysis.Normed.Lp.lpSpace
import Definitions.Def_ClassicalComplexWPT_WeightedCoefficientMap
import Theorems.Thm_ClassicalComplexWPT_norm_weightedSingleCLM_le
import Theorems.Thm_ClassicalComplexWPT_norm_lastCoefficientSeries_le

set_option autoImplicit true
open scoped NNReal ENNReal Topology
open ClassicalComplexWPT
set_option maxHeartbeats 800000
namespace ClassicalComplexWPT
theorem _root_.solution {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0) (k l : ℕ) :
    ‖weightedCoordinateSeries p r k l‖ ≤
      (r : ℝ) ^ k * ‖p.changeOriginSeries k l‖ := by
  unfold weightedCoordinateSeries
  rw [ContinuousLinearMap.compFormalMultilinearSeries_apply]
  calc
    ‖(weightedSingleCLM r k).compContinuousMultilinearMap
        (lastCoefficientSeries p k l)‖ ≤
        ‖weightedSingleCLM r k‖ * ‖lastCoefficientSeries p k l‖ :=
      ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
    _ ≤ (r : ℝ) ^ k * ‖p.changeOriginSeries k l‖ :=
      mul_le_mul (norm_weightedSingleCLM_le r k) (norm_lastCoefficientSeries_le p k l)
        (norm_nonneg _) (pow_nonneg r.coe_nonneg k)
end ClassicalComplexWPT
