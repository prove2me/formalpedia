-- Prove2me | solution 1 for Ehrhart.WeightedTorusWeylRadialIntegrationBridge.radialPolar_angle_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.88399+00:00
-- url     : https://prove2.me/submissions/68ebd30e-d87b-4a52-8330-7d8d4555015f

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusWeylRepresentativeBridge_polarInterval_holomorphic_circle_mean
import Theorems.Thm_Ehrhart_WeightedTorusWeylRepresentativeBridge_radialCoordinateKernel_polar
import Theorems.Thm_Ehrhart_WeightedTorusWeylRadialIntegrationBridge_complexPolar_center_sub_eq_circleMap

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
      (r : ℂ) *
        ((Real.smoothTransition (1 - r ^ 2) : ℂ) *
          ((2 * Real.pi : ℝ) • f c)) := by
  have hangle : -Real.pi ≤ Real.pi := by
    linarith [Real.pi_pos]
  have hcircle :=
    polarInterval_holomorphic_circle_mean hf c (-r)
  have hpoint (θ : ℝ) :
      radialPolarIntegrand f c (r, θ) =
        (r : ℂ) *
          ((Real.smoothTransition (1 - r ^ 2) : ℂ) *
            f (circleMap c (-r) θ)) := by
    unfold radialPolarIntegrand
    rw [radialCoordinateKernel_polar,
      complexPolar_center_sub_eq_circleMap]
  calc
    (∫ θ : ℝ in Set.Ioo (-Real.pi) Real.pi,
      radialPolarIntegrand f c (r, θ)) =
      ∫ θ : ℝ in Set.Ioc (-Real.pi) Real.pi,
        radialPolarIntegrand f c (r, θ) :=
      MeasureTheory.integral_Ioc_eq_integral_Ioo.symm
    _ = ∫ θ : ℝ in -Real.pi..Real.pi,
      radialPolarIntegrand f c (r, θ) :=
      (intervalIntegral.integral_of_le hangle).symm
    _ = ∫ θ : ℝ in -Real.pi..Real.pi,
      (r : ℂ) *
        ((Real.smoothTransition (1 - r ^ 2) : ℂ) *
          f (circleMap c (-r) θ)) := by
        apply intervalIntegral.integral_congr
        intro θ hθ
        exact hpoint θ
    _ = (r : ℂ) *
        (∫ θ : ℝ in -Real.pi..Real.pi,
          (Real.smoothTransition (1 - r ^ 2) : ℂ) *
            f (circleMap c (-r) θ)) :=
        intervalIntegral.integral_const_mul _ _
    _ = (r : ℂ) *
        ((Real.smoothTransition (1 - r ^ 2) : ℂ) *
          (∫ θ : ℝ in -Real.pi..Real.pi,
            f (circleMap c (-r) θ))) := by
        congr 1
        exact intervalIntegral.integral_const_mul _ _
    _ = (r : ℂ) *
        ((Real.smoothTransition (1 - r ^ 2) : ℂ) *
          ((2 * Real.pi : ℝ) • f c)) := by
        rw [hcircle]
end Ehrhart.WeightedTorusWeylRadialIntegrationBridge
