-- Prove2me | solution 1 for Ehrhart.MatrixTorusBochnerIdentity.fderiv_coverAngularSmoothPartition_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.693587+00:00
-- url     : https://prove2.me/submissions/880fbdda-a8a2-429b-919f-861d0cc392bd

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MatrixTorusBochnerBridge_contDiff_angularSmoothPartition

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.MatrixTorusBochnerIdentity
open Set Function MeasureTheory Filter Matrix
open EqualitySaturatingKillingPaths WeightedTorusDistributionBridge WeightedTorusGraphWeakBridge
open ComplexKillingSaturationBridge WeightedDolbeaultBochnerIdentity MatrixTorusBochnerBridge
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff
namespace Ehrhart.MatrixTorusBochnerIdentity
theorem _root_.solution
    {n : ℕ}
    (z v : TorusCharacters.LogSpace n) :
    (fderiv ℝ (coverAngularSmoothPartition (n := n)) z) v =
      (fderiv ℝ (angularSmoothPartition (n := n))
        ((logarithmicCoordinatesEquiv n).symm z).2)
          (((logarithmicCoordinatesEquiv n).symm v).2) := by
  let P : TorusCharacters.LogSpace n →L[ℝ]
      Space n := sourceCoverAngularLinear n
  have hη : DifferentiableAt ℝ
      (angularSmoothPartition (n := n)) (P z) :=
    (contDiff_angularSmoothPartition
      (n := n) (m := 1)).differentiable (by simp) (P z)
  have hp : DifferentiableAt ℝ
      (fun w : TorusCharacters.LogSpace n => P w) z :=
    P.differentiableAt
  have hc := fderiv_comp z hη hp
  have hinner :
      fderiv ℝ
        (fun w : TorusCharacters.LogSpace n => P w) z = P :=
    P.fderiv
  change
    fderiv ℝ
      (fun w : TorusCharacters.LogSpace n =>
        angularSmoothPartition (P w)) z =
      (fderiv ℝ (angularSmoothPartition (n := n)) (P z)).comp
        (fderiv ℝ
          (fun w : TorusCharacters.LogSpace n => P w) z)
    at hc
  rw [hinner] at hc
  have ha := congrArg
    (fun A : TorusCharacters.LogSpace n →L[ℝ] ℝ => A v) hc
  exact ha
end Ehrhart.MatrixTorusBochnerIdentity
