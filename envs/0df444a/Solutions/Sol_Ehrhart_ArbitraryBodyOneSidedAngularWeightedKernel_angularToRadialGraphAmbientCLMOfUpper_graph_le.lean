-- Prove2me | solution 1 for Ehrhart.ArbitraryBodyOneSidedAngularWeightedKernel.angularToRadialGraphAmbientCLMOfUpper_graph_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:18.423054+00:00
-- url     : https://prove2.me/submissions/69c7ab95-809e-41f3-ad43-461585199a94

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_ArbitraryBodyOneSidedAngularWeightedKernel_angularToRadialGraphAmbientCLMOfUpper_smooth_mem

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.ArbitraryBodyOneSidedAngularWeightedKernel
open Set Function MeasureTheory Filter Matrix
open WeightedTorusHilbert WeightedBrascampSaturation JetEnvelopeSlopeConvergence
open ComplexKillingSaturationBridge WeightedTorusDolbeault WeightedTorusBrascampLieb
open ArbitraryBodySmoothConvexPotentialBridge
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff
namespace Ehrhart.ArbitraryBodyOneSidedAngularWeightedKernel
theorem _root_.solution
    {n : ℕ} {a : LogTorus n → ℝ}
    {φ : Space n → ℝ} {C : ℝ}
    (hφ : Continuous φ)
    (hupper : ∀ q : LogTorus n, a q ≤ φ q.1 + C) :
    (angularDolbeaultGraph a).map
      (angularToRadialGraphAmbientCLMOfUpper hφ hupper).toLinearMap ≤
        functionDolbeaultGraph 1 φ := by
  change
    ((Submodule.span ℂ
      (smoothAngularDolbeaultGraphSet a)).topologicalClosure).map
        (angularToRadialGraphAmbientCLMOfUpper hφ hupper).toLinearMap ≤
      (Submodule.span ℂ
        (smoothFunctionDolbeaultGraphSet 1 φ)).topologicalClosure
  refine (Submodule.topologicalClosure_map
    (angularToRadialGraphAmbientCLMOfUpper hφ hupper)
    (Submodule.span ℂ (smoothAngularDolbeaultGraphSet a))).trans ?_
  apply Submodule.topologicalClosure_mono
  rw [Submodule.map_span]
  apply Submodule.span_mono
  rintro _ ⟨v, hv, rfl⟩
  exact angularToRadialGraphAmbientCLMOfUpper_smooth_mem
    hφ hupper hv
end Ehrhart.ArbitraryBodyOneSidedAngularWeightedKernel
