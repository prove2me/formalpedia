-- Prove2me | solution 1 for ClassicalComplexWPT.weightedLastCoeffs_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:59:37.497475+00:00
-- url     : https://prove2.me/submissions/c5a1ec7a-83f9-4106-9e3e-5ca8e013c606

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
    (hr : (r : ℝ≥0∞) < (p.changeOrigin x).radius) (k : ℕ) :
    weightedLastCoeffs p r x hr k =
      (r : ℂ) ^ k * p.changeOrigin x k (fun _ ↦ lastDirection n) := rfl
end ClassicalComplexWPT
