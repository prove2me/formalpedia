-- Prove2me | solution 1 for Ehrhart.WeightedTorusWeylRadialIntegrationBridge.radialPolarIntegrand_eq_zero_outside_compactDomain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.88399+00:00
-- url     : https://prove2.me/submissions/6aa0b08b-c029-4bb5-b6b9-7e78b2634084

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusWeylRepresentativeBridge_radialCoordinateKernel_eq_zero_iff

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.WeightedTorusWeylRadialIntegrationBridge
open Set MeasureTheory Filter Complex
open scoped BigOperators ContDiff Convolution ENNReal Topology
open WeightedTorusWeylRepresentativeBridge
namespace Ehrhart.WeightedTorusWeylRadialIntegrationBridge
theorem _root_.solution
    (f : ℂ → ℂ) (c : ℂ)
    (p : ℝ × ℝ)
    (hp : p ∈ Complex.polarCoord.target)
    (houtside : p ∉ compactPolarDomain) :
    radialPolarIntegrand f c p = 0 := by
  rw [Complex.polarCoord_target] at hp
  have hr : ¬p.1 ≤ 1 := by
    intro hle
    apply houtside
    exact ⟨⟨hp.1, hle⟩, hp.2⟩
  have hnorm : 1 ≤ ‖Complex.polarCoord.symm p‖ := by
    rw [Complex.norm_polarCoord_symm,
      abs_of_pos hp.1]
    exact le_of_lt (lt_of_not_ge hr)
  have hzero :=
    (radialCoordinateKernel_eq_zero_iff
      (Complex.polarCoord.symm p)).2 hnorm
  change
    (p.1 : ℂ) *
      ((radialCoordinateKernel (Complex.polarCoord.symm p) : ℂ) *
        f (c - Complex.polarCoord.symm p)) = 0
  rw [hzero]
  simp
end Ehrhart.WeightedTorusWeylRadialIntegrationBridge
