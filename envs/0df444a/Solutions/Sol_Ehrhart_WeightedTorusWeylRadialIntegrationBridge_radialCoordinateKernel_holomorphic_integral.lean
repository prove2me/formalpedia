-- Prove2me | solution 1 for Ehrhart.WeightedTorusWeylRadialIntegrationBridge.radialCoordinateKernel_holomorphic_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.88399+00:00
-- url     : https://prove2.me/submissions/edfb3f76-80c6-4b8b-b1c2-e92dc9d69dc9

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusWeylRadialIntegrationBridge_radialCoordinateKernel_integral_eq_polar
import Theorems.Thm_Ehrhart_WeightedTorusWeylRadialIntegrationBridge_radialPolarIntegral_eq_compactDomain
import Theorems.Thm_Ehrhart_WeightedTorusWeylRadialIntegrationBridge_radialPolar_compact_integral_eq_iterated
import Theorems.Thm_Ehrhart_WeightedTorusWeylRadialIntegrationBridge_radialPolar_angle_integral_eq_one_mul_center

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
    (c : ℂ) :
    (∫ w : ℂ,
      radialCoordinateKernel w • f (c - w)) =
      (∫ w : ℂ, radialCoordinateKernel w) • f c := by
  have hone : Differentiable ℂ (fun _ : ℂ => (1 : ℂ)) := by
    fun_prop
  calc
    (∫ w : ℂ,
      radialCoordinateKernel w • f (c - w)) =
      ∫ p : ℝ × ℝ in Complex.polarCoord.target,
        radialPolarIntegrand f c p :=
      radialCoordinateKernel_integral_eq_polar f c
    _ = ∫ p : ℝ × ℝ in compactPolarDomain,
        radialPolarIntegrand f c p :=
      radialPolarIntegral_eq_compactDomain f c
    _ = ∫ r : ℝ in Set.Ioc (0 : ℝ) 1,
        ∫ θ : ℝ in Set.Ioo (-Real.pi) Real.pi,
          radialPolarIntegrand f c (r, θ) :=
      radialPolar_compact_integral_eq_iterated hf c
    _ = ∫ r : ℝ in Set.Ioc (0 : ℝ) 1,
        ((∫ θ : ℝ in Set.Ioo (-Real.pi) Real.pi,
          radialPolarIntegrand (fun _ : ℂ => (1 : ℂ)) 0 (r, θ)) *
            f c) := by
      apply integral_congr_ae
      filter_upwards [] with r
      exact radialPolar_angle_integral_eq_one_mul_center hf c r
    _ = (∫ r : ℝ in Set.Ioc (0 : ℝ) 1,
          ∫ θ : ℝ in Set.Ioo (-Real.pi) Real.pi,
            radialPolarIntegrand (fun _ : ℂ => (1 : ℂ))
              0 (r, θ)) * f c :=
      MeasureTheory.integral_mul_const _ _
    _ = (∫ p : ℝ × ℝ in compactPolarDomain,
          radialPolarIntegrand (fun _ : ℂ => (1 : ℂ)) 0 p) *
            f c := by
      rw [radialPolar_compact_integral_eq_iterated hone 0]
    _ = (∫ p : ℝ × ℝ in Complex.polarCoord.target,
          radialPolarIntegrand (fun _ : ℂ => (1 : ℂ)) 0 p) *
            f c := by
      rw [radialPolarIntegral_eq_compactDomain]
    _ = (∫ w : ℂ,
          radialCoordinateKernel w • (1 : ℂ)) * f c := by
      rw [radialCoordinateKernel_integral_eq_polar
        (fun _ : ℂ => (1 : ℂ)) 0]
    _ = (∫ w : ℂ, radialCoordinateKernel w) • f c := by
      simp only [Complex.real_smul, mul_one]
      exact congrArg (fun w : ℂ => w * f c)
        (integral_complex_ofReal (f := radialCoordinateKernel))
end Ehrhart.WeightedTorusWeylRadialIntegrationBridge
