-- Prove2me | solution 1 for ClassicalComplexWPT.normalizedOriginCoeffs_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:03:09.86003+00:00
-- url     : https://prove2.me/submissions/b1458c3d-3c77-4ac6-867c-1737dfbe7a4b

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
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) (d k : ℕ) :
    normalizedOriginCoeffs p r hr d k =
      (((r : ℂ) ^ d * lastTaylorCoefficient p d 0)⁻¹) *
        ((r : ℂ) ^ k * lastTaylorCoefficient p k 0) := rfl
end ClassicalComplexWPT
