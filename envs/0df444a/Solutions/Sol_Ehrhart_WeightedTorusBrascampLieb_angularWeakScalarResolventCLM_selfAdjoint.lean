-- Prove2me | solution 1 for Ehrhart.WeightedTorusBrascampLieb.angularWeakScalarResolventCLM_selfAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:18.423054+00:00
-- url     : https://prove2.me/submissions/7735e604-71e3-4879-be54-d8fb5670f641

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusDolbeault_angularWeakDolbeaultResolvent_moment_components

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
theorem _root_.solution {n : ℕ}
    (a : LogTorus n → ℝ) (f g : angularWeightedScalarL2 a) :
    @inner ℂ (angularWeightedScalarL2 a) _
      (angularWeakScalarResolventCLM a f) g =
      @inner ℂ (angularWeightedScalarL2 a) _ f
        (angularWeakScalarResolventCLM a g) := by
  have hfg := angularWeakDolbeaultResolvent_moment_components
    a f (angularWeakDolbeaultResolvent a g)
  have hgf := angularWeakDolbeaultResolvent_moment_components
    a g (angularWeakDolbeaultResolvent a f)
  have hgf' := congrArg conj hgf
  simp only [map_add, inner_conj_symm] at hgf'
  rw [angularWeakScalarResolventCLM_apply,
    angularWeakScalarResolventCLM_apply]
  exact hgf'.symm.trans hfg
end Ehrhart.WeightedTorusBrascampLieb
