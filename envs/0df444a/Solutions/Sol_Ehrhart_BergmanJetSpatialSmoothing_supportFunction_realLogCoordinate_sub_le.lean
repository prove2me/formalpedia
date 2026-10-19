-- Prove2me | solution 1 for Ehrhart.BergmanJetSpatialSmoothing.supportFunction_realLogCoordinate_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:18.423054+00:00
-- url     : https://prove2.me/submissions/505f48e2-3865-474b-b04e-e45601b0725f

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetSpatialSmoothing_dist_realLogCoordinate_sub_le

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetSpatialSmoothing
open Set Function Filter MeasureTheory
open TorusCharacters BergmanDiagonalBasisIndependence ArbitraryBodySmoothConvexPotentialBridge
open scoped BigOperators Topology Convolution ContDiff
namespace Ehrhart.BergmanJetSpatialSmoothing
theorem _root_.solution
    {n : ℕ} (K : CenteredBody n)
    {R : ℝ} (hR₀ : 0 ≤ R)
    (hR : ∀ u ∈ K.carrier, ‖u‖ ≤ R)
    (z y : LogSpace n) :
    SupportFunction.supportFunction K.carrier
        (realLogCoordinate (z - y)) ≤
      SupportFunction.supportFunction K.carrier
          (realLogCoordinate z) +
        ((n : ℝ) * R) * (2 * ‖y‖) := by
  have hnR : 0 ≤ (n : ℝ) * R :=
    mul_nonneg (Nat.cast_nonneg n) hR₀
  have hlip := supportFunction_lipschitzWith K.compact
    (K.fullDimensional.mono interior_subset) hR
  have hdist := hlip.dist_le_mul
    (realLogCoordinate (z - y)) (realLogCoordinate z)
  rw [Real.coe_toNNReal _ hnR] at hdist
  calc
    SupportFunction.supportFunction K.carrier
        (realLogCoordinate (z - y)) ≤
      SupportFunction.supportFunction K.carrier
          (realLogCoordinate z) +
        dist
          (SupportFunction.supportFunction K.carrier
            (realLogCoordinate (z - y)))
          (SupportFunction.supportFunction K.carrier
            (realLogCoordinate z)) := by
      rw [Real.dist_eq]
      linarith [le_abs_self
        (SupportFunction.supportFunction K.carrier
          (realLogCoordinate (z - y)) -
          SupportFunction.supportFunction K.carrier
            (realLogCoordinate z))]
    _ ≤ SupportFunction.supportFunction K.carrier
          (realLogCoordinate z) +
        ((n : ℝ) * R) *
          dist (realLogCoordinate (z - y))
            (realLogCoordinate z) :=
      add_le_add (le_refl _) hdist
    _ ≤ SupportFunction.supportFunction K.carrier
          (realLogCoordinate z) +
        ((n : ℝ) * R) * (2 * ‖y‖) :=
      add_le_add (le_refl _)
        (mul_le_mul_of_nonneg_left
          (dist_realLogCoordinate_sub_le z y) hnR)
end Ehrhart.BergmanJetSpatialSmoothing
