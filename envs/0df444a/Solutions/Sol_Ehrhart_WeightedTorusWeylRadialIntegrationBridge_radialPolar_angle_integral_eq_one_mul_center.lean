-- Prove2me | solution 1 for Ehrhart.WeightedTorusWeylRadialIntegrationBridge.radialPolar_angle_integral_eq_one_mul_center
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.88399+00:00
-- url     : https://prove2.me/submissions/c1b9333c-3781-4c7c-afb2-79f32ea07133

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusWeylRadialIntegrationBridge_radialPolar_angle_integral

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
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (c : ℂ) (r : ℝ) :
    (∫ θ : ℝ in Set.Ioo (-Real.pi) Real.pi,
      radialPolarIntegrand f c (r, θ)) =
      (∫ θ : ℝ in Set.Ioo (-Real.pi) Real.pi,
        radialPolarIntegrand (fun _ : ℂ => (1 : ℂ)) 0 (r, θ)) *
          f c := by
  have hone : Differentiable ℂ (fun _ : ℂ => (1 : ℂ)) := by
    fun_prop
  rw [radialPolar_angle_integral hf c r,
    radialPolar_angle_integral hone 0 r]
  simp only [Complex.real_smul, mul_one]
  ring
end Ehrhart.WeightedTorusWeylRadialIntegrationBridge
