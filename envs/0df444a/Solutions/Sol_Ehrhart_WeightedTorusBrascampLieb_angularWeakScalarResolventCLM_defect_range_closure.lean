-- Prove2me | solution 1 for Ehrhart.WeightedTorusBrascampLieb.angularWeakScalarResolventCLM_defect_range_closure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:18.423054+00:00
-- url     : https://prove2.me/submissions/25b29fc9-2d05-4bc2-b02c-a89855c769a3

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusBrascampLieb_angularWeakScalarResolventCLM_selfAdjoint

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.WeightedTorusBrascampLieb
open Set Function MeasureTheory Filter Matrix
open WeightedTorusHilbert WeightedBrascampSaturation ComplexKillingSaturationBridge
open ComplexSaturatedKillingFieldBridge WeightedTorusWeylWeakRepresentativeBridge
open JointHolomorphicLaurentFourierCompatibility WeightedTorusDolbeault WeightedTorusBochner
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff
namespace Ehrhart.WeightedTorusBrascampLieb
theorem _root_.solution
    {n : ℕ} (a : LogTorus n → ℝ) :
    ((ContinuousLinearMap.id ℂ (angularWeightedScalarL2 a) -
      angularWeakScalarResolventCLM a).range).topologicalClosure =
      (angularWeakResolventFixedSpace a)ᗮ := by
  let T : angularWeightedScalarL2 a →L[ℂ]
      angularWeightedScalarL2 a :=
    ContinuousLinearMap.id ℂ (angularWeightedScalarL2 a) -
      angularWeakScalarResolventCLM a
  have hTadj : T.adjoint = T := by
    symm
    apply (ContinuousLinearMap.eq_adjoint_iff T T).2
    intro x y
    change
      @inner ℂ (angularWeightedScalarL2 a) _
        (x - angularWeakScalarResolventCLM a x) y =
        @inner ℂ (angularWeightedScalarL2 a) _ x
          (y - angularWeakScalarResolventCLM a y)
    rw [inner_sub_left, inner_sub_right,
      angularWeakScalarResolventCLM_selfAdjoint]
  have hker : T.ker = angularWeakResolventFixedSpace a := by
    ext x
    change
      x - angularWeakScalarResolventCLM a x = 0 ↔
        angularWeakScalarResolventCLM a x = x
    rw [sub_eq_zero]
    exact eq_comm
  change T.range.topologicalClosure =
    (angularWeakResolventFixedSpace a)ᗮ
  calc
    T.range.topologicalClosure = T.kerᗮ := by
      simpa only [hTadj] using (T.orthogonal_ker).symm
    _ = (angularWeakResolventFixedSpace a)ᗮ := by rw [hker]
end Ehrhart.WeightedTorusBrascampLieb
