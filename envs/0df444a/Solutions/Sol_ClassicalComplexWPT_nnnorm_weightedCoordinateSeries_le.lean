-- Prove2me | solution 1 for ClassicalComplexWPT.nnnorm_weightedCoordinateSeries_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:04:55.829282+00:00
-- url     : https://prove2.me/submissions/13e2fd0e-845e-489c-8034-79f271e6fe19

import Definitions.Def_ClassicalComplexWPT_AnalyticSeries
import Mathlib.Analysis.Normed.Lp.lpSpace
import Definitions.Def_ClassicalComplexWPT_WeightedCoefficientMap
import Theorems.Thm_ClassicalComplexWPT_norm_weightedCoordinateSeries_le
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
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0) (k l : ℕ) :
    ‖weightedCoordinateSeries p r k l‖₊ ≤
      ‖p.changeOriginSeries k l‖₊ * r ^ k := by
  apply NNReal.coe_le_coe.mp
  push_cast
  simpa [mul_comm] using norm_weightedCoordinateSeries_le p r k l
end ClassicalComplexWPT
