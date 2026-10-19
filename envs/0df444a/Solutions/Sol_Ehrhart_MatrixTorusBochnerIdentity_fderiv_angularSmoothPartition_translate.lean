-- Prove2me | solution 1 for Ehrhart.MatrixTorusBochnerIdentity.fderiv_angularSmoothPartition_translate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.121018+00:00
-- url     : https://prove2.me/submissions/bf2c5c2a-f727-41cc-b88b-4480ac420b6a

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
    {n : ℕ} (b t : Space n) :
    fderiv ℝ (fun s : Space n =>
      angularSmoothPartition (b + s)) t =
      fderiv ℝ (angularSmoothPartition (n := n)) (b + t) := by
  have hbump : DifferentiableAt ℝ
      (angularSmoothPartition (n := n)) (b + t) :=
    (contDiff_angularSmoothPartition (n := n) (m := 1)).differentiable
      (by simp) (b + t)
  have hshift : DifferentiableAt ℝ
      (fun s : Space n => b + s) t := by
    fun_prop
  have hinner :
      fderiv ℝ (fun s : Space n => b + s) t =
        ContinuousLinearMap.id ℝ (Space n) := by
    simpa [fderiv_fun_id] using
      (fderiv_const_add (𝕜 := ℝ)
        (f := fun s : Space n => s) (x := t) b)
  have hcomp := fderiv_comp t hbump hshift
  change
    fderiv ℝ
      (fun s : Space n => angularSmoothPartition (b + s)) t =
      (fderiv ℝ (angularSmoothPartition (n := n)) (b + t)).comp
        (fderiv ℝ (fun s : Space n => b + s) t)
    at hcomp
  rw [hinner, ContinuousLinearMap.comp_id] at hcomp
  exact hcomp
end Ehrhart.MatrixTorusBochnerIdentity
