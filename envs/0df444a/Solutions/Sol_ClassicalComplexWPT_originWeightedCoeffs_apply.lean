-- Prove2me | solution 1 for ClassicalComplexWPT.originWeightedCoeffs_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:01:36.056625+00:00
-- url     : https://prove2.me/submissions/0ac730c5-940b-4e10-9a11-b70b7777fa9d

import Definitions.Def_ClassicalComplexWPT_AnalyticSeries
import Definitions.Def_ClassicalComplexWPT_ExactOrder
import Definitions.Def_ClassicalComplexWPT_WeightedSeries
import Definitions.Def_ClassicalComplexWPT_WeightedCoefficientMap
import Definitions.Def_ClassicalComplexWPT_NormalizedCoefficients

set_option autoImplicit true
open Filter
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
set_option maxHeartbeats 1000000
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (R : ℝ≥0)
    (hR : (R : ℝ≥0∞) < p.radius) (k : ℕ) :
    originWeightedCoeffs p R hR k =
      (R : ℂ) ^ k * lastTaylorCoefficient p k 0 := rfl
end ClassicalComplexWPT
