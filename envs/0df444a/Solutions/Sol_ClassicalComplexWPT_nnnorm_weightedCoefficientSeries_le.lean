-- Prove2me | solution 1 for ClassicalComplexWPT.nnnorm_weightedCoefficientSeries_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:06:40.769177+00:00
-- url     : https://prove2.me/submissions/0a61005f-c2f9-4901-8553-2ac8b609a02d

import Definitions.Def_ClassicalComplexWPT_AnalyticSeries
import Mathlib.Analysis.Normed.Lp.lpSpace
import Definitions.Def_ClassicalComplexWPT_WeightedCoefficientMap
import Theorems.Thm_ClassicalComplexWPT_nnnorm_weightedCoordinateSeries_le
import Theorems.Thm_ClassicalComplexWPT_summable_nnnorm_changeOriginSeries_mul_pow
import Theorems.Thm_ClassicalComplexWPT_summable_nnnorm_weightedCoordinateSeries

set_option autoImplicit true
open scoped NNReal ENNReal Topology
open ClassicalComplexWPT
set_option maxHeartbeats 800000
namespace ClassicalComplexWPT
theorem _root_.solution {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) (l : ℕ) :
    ‖weightedCoefficientSeries p r l‖₊ ≤
      ∑' k : ℕ, ‖p.changeOriginSeries k l‖₊ * r ^ k := by
  unfold weightedCoefficientSeries
  calc
    ‖∑' k : ℕ, weightedCoordinateSeries p r k l‖₊ ≤
        ∑' k : ℕ, ‖weightedCoordinateSeries p r k l‖₊ :=
      nnnorm_tsum_le (summable_nnnorm_weightedCoordinateSeries p r hr l)
    _ ≤ ∑' k : ℕ, ‖p.changeOriginSeries k l‖₊ * r ^ k := by
      apply Summable.tsum_le_tsum
      · intro k
        exact nnnorm_weightedCoordinateSeries_le p r k l
      · exact summable_nnnorm_weightedCoordinateSeries p r hr l
      · exact summable_nnnorm_changeOriginSeries_mul_pow p r hr l
end ClassicalComplexWPT
