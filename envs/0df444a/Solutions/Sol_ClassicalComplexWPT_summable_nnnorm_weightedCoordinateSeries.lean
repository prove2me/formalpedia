-- Prove2me | solution 1 for ClassicalComplexWPT.summable_nnnorm_weightedCoordinateSeries
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:05:57.869358+00:00
-- url     : https://prove2.me/submissions/24e841f8-c578-4b93-80a6-15b9d2b84043

import Definitions.Def_ClassicalComplexWPT_AnalyticSeries
import Mathlib.Analysis.Normed.Lp.lpSpace
import Definitions.Def_ClassicalComplexWPT_WeightedCoefficientMap
import Theorems.Thm_ClassicalComplexWPT_nnnorm_weightedCoordinateSeries_le
import Theorems.Thm_ClassicalComplexWPT_summable_nnnorm_changeOriginSeries_mul_pow

set_option autoImplicit true
open scoped NNReal ENNReal Topology
open ClassicalComplexWPT
set_option maxHeartbeats 800000
namespace ClassicalComplexWPT
theorem _root_.solution {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) (l : ℕ) :
    Summable (fun k : ℕ ↦ ‖weightedCoordinateSeries p r k l‖₊) := by
  refine NNReal.summable_of_le (fun k ↦ ?_)
    (summable_nnnorm_changeOriginSeries_mul_pow p r hr l)
  exact nnnorm_weightedCoordinateSeries_le p r k l
end ClassicalComplexWPT
