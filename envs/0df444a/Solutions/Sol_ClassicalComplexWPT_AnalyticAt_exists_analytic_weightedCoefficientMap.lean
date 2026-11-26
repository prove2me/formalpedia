-- Prove2me | solution 1 for ClassicalComplexWPT.AnalyticAt.exists_analytic_weightedCoefficientMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:14:49.021945+00:00
-- url     : https://prove2.me/submissions/5c0775a4-319d-46e1-b5f6-c4914418c98c

import Definitions.Def_ClassicalComplexWPT_AnalyticSeries
import Mathlib.Analysis.Normed.Lp.lpSpace
import Definitions.Def_ClassicalComplexWPT_WeightedCoefficientMap
import Theorems.Thm_ClassicalComplexWPT_analyticAt_weightedCoefficientSeries_sum

set_option autoImplicit true
open scoped NNReal ENNReal Topology
open ClassicalComplexWPT
set_option maxHeartbeats 800000
namespace ClassicalComplexWPT
namespace AnalyticAt
theorem _root_.solution {n : ℕ}
    {f : Ambient n → ℂ} (hf : AnalyticAt ℂ f 0) :
    ∃ (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0),
      HasFPowerSeriesAt f p 0 ∧ 0 < r ∧
        AnalyticAt ℂ (weightedCoefficientSeries p r).sum 0 := by
  obtain ⟨p, hp⟩ := hf
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 hp.radius_pos with ⟨r, hr0, hrp⟩
  have hr0' : (0 : ℝ≥0) < r := by exact_mod_cast hr0
  exact ⟨p, r, hp, hr0', analyticAt_weightedCoefficientSeries_sum p r hrp⟩
end AnalyticAt
end ClassicalComplexWPT
