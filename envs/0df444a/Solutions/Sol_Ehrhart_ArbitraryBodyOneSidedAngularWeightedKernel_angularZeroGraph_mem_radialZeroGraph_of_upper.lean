-- Prove2me | solution 1 for Ehrhart.ArbitraryBodyOneSidedAngularWeightedKernel.angularZeroGraph_mem_radialZeroGraph_of_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:18.423054+00:00
-- url     : https://prove2.me/submissions/1a1a3169-11d5-42cd-b002-2cc7ca76eb89

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_ArbitraryBodyOneSidedAngularWeightedKernel_angularToRadialGraphAmbientCLMOfUpper_graph_le

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
    (hupper : ∀ q : LogTorus n, a q ≤ φ q.1 + C)
    (f : angularWeightedScalarL2 a)
    (hf : WithLp.toLp 2
      (f, (0 : angularWeightedFormL2 a)) ∈
        angularDolbeaultGraph a) :
    WithLp.toLp 2
      (angularToRadialLpOfUpper hφ hupper f,
       (0 : weightedTorusFormL2 1 φ)) ∈
        functionDolbeaultGraph 1 φ := by
  have hmap :=
    angularToRadialGraphAmbientCLMOfUpper_graph_le hφ hupper
      (Submodule.mem_map.mpr
        ⟨WithLp.toLp 2 (f, (0 : angularWeightedFormL2 a)),
          hf, rfl⟩)
  simpa using hmap
end Ehrhart.ArbitraryBodyOneSidedAngularWeightedKernel
