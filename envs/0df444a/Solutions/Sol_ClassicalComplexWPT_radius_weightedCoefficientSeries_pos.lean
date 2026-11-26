-- Prove2me | solution 1 for ClassicalComplexWPT.radius_weightedCoefficientSeries_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:08:04.023145+00:00
-- url     : https://prove2.me/submissions/6ca13b47-a896-4b7b-b6ad-acc303927187

import Definitions.Def_ClassicalComplexWPT_AnalyticSeries
import Mathlib.Analysis.Normed.Lp.lpSpace
import Definitions.Def_ClassicalComplexWPT_WeightedCoefficientMap
import Theorems.Thm_ClassicalComplexWPT_le_radius_weightedCoefficientSeries
import Theorems.Thm_ClassicalComplexWPT_lastAxis_apply
import Theorems.Thm_ClassicalComplexWPT_lastSlice_zero
attribute [local simp] ClassicalComplexWPT.lastAxis_apply
attribute [local simp] ClassicalComplexWPT.lastSlice_zero



set_option autoImplicit true
open scoped NNReal ENNReal Topology
open ClassicalComplexWPT
set_option maxHeartbeats 800000
namespace ClassicalComplexWPT
theorem _root_.solution {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) :
    0 < (weightedCoefficientSeries p r).radius := by
  rcases ENNReal.lt_iff_exists_add_pos_lt.1 hr with ⟨s, hs, hrs⟩
  have hsr : (s + r : ℝ≥0∞) < p.radius := by simpa [add_comm] using hrs
  exact (show (0 : ℝ≥0∞) < s by simpa using hs).trans_le
    (le_radius_weightedCoefficientSeries p s r hsr)
end ClassicalComplexWPT
