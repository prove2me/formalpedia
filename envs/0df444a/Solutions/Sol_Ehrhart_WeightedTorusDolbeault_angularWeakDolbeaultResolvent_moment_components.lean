-- Prove2me | solution 1 for Ehrhart.WeightedTorusDolbeault.angularWeakDolbeaultResolvent_moment_components
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.693587+00:00
-- url     : https://prove2.me/submissions/3dca7aa5-a1ee-4cb4-a8e1-036d86a23351

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusDolbeault_angularWeakDolbeaultResolvent_moment

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.WeightedTorusDolbeault
open Set Function MeasureTheory Filter Matrix
open WeightedTorusHilbert JetEnvelopeSlopeConvergence ComplexKillingSaturationBridge
open WeightedTorusDistributionBridge MatrixTorusBochnerIdentity
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff
namespace Ehrhart.WeightedTorusDolbeault
theorem _root_.solution {n : ℕ}
    (a : LogTorus n → ℝ)
    (f : angularWeightedScalarL2 a)
    (v : angularDolbeaultGraph a) :
    @inner ℂ (angularWeightedScalarL2 a) _
      (WithLp.fst (angularWeakDolbeaultResolvent a f :
        angularDolbeaultGraphAmbient a))
      (WithLp.fst (v : angularDolbeaultGraphAmbient a)) +
    @inner ℂ (angularWeightedFormL2 a) _
      (WithLp.snd (angularWeakDolbeaultResolvent a f :
        angularDolbeaultGraphAmbient a))
      (WithLp.snd (v : angularDolbeaultGraphAmbient a)) =
    @inner ℂ (angularWeightedScalarL2 a) _ f
      (WithLp.fst (v : angularDolbeaultGraphAmbient a)) := by
  have h := angularWeakDolbeaultResolvent_moment a f v
  rw [inner_sub_left] at h
  simp only [WithLp.prod_inner_apply, inner_zero_left, add_zero] at h
  exact (sub_eq_zero.mp h).symm
end Ehrhart.WeightedTorusDolbeault
