-- Prove2me | solution 1 for ClassicalComplexWPT.radius_weightedLastCoeffs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:00:03.36482+00:00
-- url     : https://prove2.me/submissions/72b92e81-c74c-4f0f-8cbb-5558b8083319

import Definitions.Def_ClassicalComplexWPT_AnalyticSeries
import Mathlib.Analysis.Normed.Lp.lpSpace
import Definitions.Def_ClassicalComplexWPT_WeightedCoefficientMap

set_option autoImplicit true
open scoped NNReal ENNReal Topology
open ClassicalComplexWPT
set_option maxHeartbeats 800000
namespace ClassicalComplexWPT
theorem _root_.solution {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0) (x : Ambient n)
    (h : (‖x‖₊ + r : ℝ≥0∞) < p.radius) :
    (r : ℝ≥0∞) < (p.changeOrigin x).radius := by
  refine lt_of_lt_of_le ?_ p.changeOrigin_radius
  rwa [lt_tsub_iff_right, add_comm]
end ClassicalComplexWPT
