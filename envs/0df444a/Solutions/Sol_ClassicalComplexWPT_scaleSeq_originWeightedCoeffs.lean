-- Prove2me | solution 1 for ClassicalComplexWPT.scaleSeq_originWeightedCoeffs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:06:53.773444+00:00
-- url     : https://prove2.me/submissions/00ebd756-0b56-4524-99c1-7ed717447954

import Definitions.Def_ClassicalComplexWPT_AnalyticSeries
import Definitions.Def_ClassicalComplexWPT_ExactOrder
import Definitions.Def_ClassicalComplexWPT_WeightedSeries
import Definitions.Def_ClassicalComplexWPT_WeightedCoefficientMap
import Definitions.Def_ClassicalComplexWPT_NormalizedCoefficients
import Theorems.Thm_ClassicalComplexWPT_originWeightedCoeffs_apply
import Theorems.Thm_ClassicalComplexWPT_lastAxis_apply
import Theorems.Thm_ClassicalComplexWPT_lastSlice_zero
import Theorems.Thm_ClassicalComplexWPT_monomial_zero
import Theorems.Thm_ClassicalComplexWPT_weightedLastCoeffs_apply
attribute [local simp] ClassicalComplexWPT.lastAxis_apply
attribute [local simp] ClassicalComplexWPT.lastSlice_zero
attribute [local simp] ClassicalComplexWPT.monomial_zero
attribute [local simp] ClassicalComplexWPT.weightedLastCoeffs_apply


attribute [local simp] ClassicalComplexWPT.originWeightedCoeffs_apply

set_option autoImplicit true
open Filter
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
set_option maxHeartbeats 1000000
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (R t : ℝ≥0)
    (hR : (R : ℝ≥0∞) < p.radius) (ht : t ≤ 1) :
    scaleSeq t ht (originWeightedCoeffs p R hR) =
      originWeightedCoeffs p (t * R) (mul_radius_lt_of_le_one p R t hR ht) := by
  apply lp.ext
  funext k
  simp only [scaleSeq_apply, originWeightedCoeffs_apply]
  push_cast
  rw [mul_pow]
  ring
end ClassicalComplexWPT
