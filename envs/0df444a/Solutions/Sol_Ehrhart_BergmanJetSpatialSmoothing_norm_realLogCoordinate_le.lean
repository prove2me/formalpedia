-- Prove2me | solution 1 for Ehrhart.BergmanJetSpatialSmoothing.norm_realLogCoordinate_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:18.423054+00:00
-- url     : https://prove2.me/submissions/121729d0-1769-4158-b3ba-92e3da7a6048

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

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
theorem _root_.solution {n : ℕ} (z : LogSpace n) :
    ‖realLogCoordinate z‖ ≤ 2 * ‖z‖ := by
  apply (pi_norm_le_iff_of_nonneg
    (mul_nonneg (by norm_num) (norm_nonneg z))).2
  intro j
  calc
    ‖realLogCoordinate z j‖ = 2 * |(z j).re| := by
      simp [realLogCoordinate, Real.norm_eq_abs]
    _ ≤ 2 * ‖z j‖ :=
      mul_le_mul_of_nonneg_left
        (Complex.abs_re_le_norm (z j)) (by norm_num)
    _ ≤ 2 * ‖z‖ :=
      mul_le_mul_of_nonneg_left
        (norm_le_pi_norm z j) (by norm_num)
end Ehrhart.BergmanJetSpatialSmoothing
