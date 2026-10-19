-- Prove2me | solution 1 for Ehrhart.JointHolomorphicLaurentFourierCompatibility.unit_interval_vertical_integral_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:12.519086+00:00
-- url     : https://prove2.me/submissions/f7640a95-aba1-42d7-9c33-e33d1c7668db

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_HolomorphicLaurentFourierCompletenessBridge_periodic_holomorphic_vertical_integral_eq

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.JointHolomorphicLaurentFourierCompatibility
open Set MeasureTheory Filter Complex
open scoped BigOperators ComplexConjugate ENNReal Topology InnerProductSpace
attribute [local instance] Ehrhart.JointHolomorphicLaurentFourierCompatibility._p2m_local_instance_3610026555_13915
attribute [local instance] Ehrhart.JointHolomorphicLaurentFourierCompatibility._p2m_local_instance_3610026555_13918
namespace Ehrhart.JointHolomorphicLaurentFourierCompatibility
theorem _root_.solution
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hperiod : Function.Periodic f
      HolomorphicLaurentFourierCompletenessBridge.logarithmicPeriod)
    (a b : ℝ) :
    (∫ t : ℝ in 0..1,
      f ((b : ℂ) +
        (2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ))) =
      ∫ t : ℝ in 0..1,
        f ((a : ℂ) +
          (2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ)) := by
  have hcg :=
    HolomorphicLaurentFourierCompletenessBridge.periodic_holomorphic_vertical_integral_eq
      hf hperiod a b
  have hπ : (2 * Real.pi : ℝ) ≠ 0 :=
    ne_of_gt Real.two_pi_pos
  have hscale (r : ℝ) :
      (∫ t : ℝ in 0..1,
        f ((r : ℂ) +
          (2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ))) =
        (2 * Real.pi : ℝ)⁻¹ •
          (∫ t : ℝ in 0..2 * Real.pi,
            f ((r : ℂ) + (t : ℂ) * Complex.I)) := by
    have h := intervalIntegral.integral_comp_mul_left
      (a := (0 : ℝ)) (b := (1 : ℝ))
      (c := 2 * Real.pi)
      (fun t : ℝ => f ((r : ℂ) + (t : ℂ) * Complex.I)) hπ
    calc
      (∫ t : ℝ in 0..1,
        f ((r : ℂ) +
          (2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ))) =
        ∫ t : ℝ in 0..1,
          f ((r : ℂ) + ((2 * Real.pi * t : ℝ) : ℂ) *
            Complex.I) := by
          apply intervalIntegral.integral_congr
          intro t ht
          push_cast
          ring_nf
      _ = (2 * Real.pi : ℝ)⁻¹ •
          (∫ t : ℝ in (2 * Real.pi) * 0..(2 * Real.pi) * 1,
            f ((r : ℂ) + (t : ℂ) * Complex.I)) := h
      _ = _ := by simp only [mul_zero, mul_one]
  rw [hscale b, hscale a, hcg]
end Ehrhart.JointHolomorphicLaurentFourierCompatibility
