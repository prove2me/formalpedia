-- Prove2me | solution 1 for ClassicalComplexWPT.norm_weightedSingleCLM_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:00:01.981009+00:00
-- url     : https://prove2.me/submissions/fa828de5-08a7-4098-b379-f1d04ae3c630

import Definitions.Def_ClassicalComplexWPT_AnalyticSeries
import Mathlib.Analysis.Normed.Lp.lpSpace
import Definitions.Def_ClassicalComplexWPT_WeightedCoefficientMap

set_option autoImplicit true
open scoped NNReal ENNReal Topology
open ClassicalComplexWPT
set_option maxHeartbeats 800000
namespace ClassicalComplexWPT
theorem _root_.solution (r : ℝ≥0) (k : ℕ) :
    ‖weightedSingleCLM r k‖ ≤ (r : ℝ) ^ k := by
  exact ContinuousLinearMap.opNorm_le_bound (weightedSingleCLM r k)
    (pow_nonneg r.coe_nonneg k) (fun z ↦ by
      rw [weightedSingleCLM_apply, lp.norm_single (by norm_num), norm_mul, norm_pow,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg r.coe_nonneg])
end ClassicalComplexWPT
