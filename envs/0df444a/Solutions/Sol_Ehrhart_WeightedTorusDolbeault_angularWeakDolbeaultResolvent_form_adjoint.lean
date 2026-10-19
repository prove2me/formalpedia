-- Prove2me | solution 1 for Ehrhart.WeightedTorusDolbeault.angularWeakDolbeaultResolvent_form_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.693587+00:00
-- url     : https://prove2.me/submissions/ab71506d-b27d-46ff-a248-b66d1f461349

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
    @inner ℂ (angularWeightedFormL2 a) _
      (WithLp.snd (angularWeakDolbeaultResolvent a f :
        angularDolbeaultGraphAmbient a))
      (WithLp.snd (v : angularDolbeaultGraphAmbient a)) =
    @inner ℂ (angularWeightedScalarL2 a) _
      (f - WithLp.fst (angularWeakDolbeaultResolvent a f :
        angularDolbeaultGraphAmbient a))
      (WithLp.fst (v : angularDolbeaultGraphAmbient a)) := by
  rw [inner_sub_left]
  have h := angularWeakDolbeaultResolvent_moment_components a f v
  linear_combination h
end Ehrhart.WeightedTorusDolbeault
