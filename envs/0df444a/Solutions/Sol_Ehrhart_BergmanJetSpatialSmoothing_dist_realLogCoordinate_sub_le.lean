-- Prove2me | solution 1 for Ehrhart.BergmanJetSpatialSmoothing.dist_realLogCoordinate_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:18.423054+00:00
-- url     : https://prove2.me/submissions/3fe16d4e-1782-4c05-85ba-c8d5f00b8993

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetSpatialSmoothing_norm_realLogCoordinate_le

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
    {n : ℕ} (z y : LogSpace n) :
    dist (realLogCoordinate (z - y))
      (realLogCoordinate z) ≤ 2 * ‖y‖ := by
  rw [dist_eq_norm]
  have heq : realLogCoordinate (z - y) -
      realLogCoordinate z = -realLogCoordinate y := by
    funext j
    simp [realLogCoordinate]
    ring
  rw [heq, norm_neg]
  exact norm_realLogCoordinate_le y
end Ehrhart.BergmanJetSpatialSmoothing
