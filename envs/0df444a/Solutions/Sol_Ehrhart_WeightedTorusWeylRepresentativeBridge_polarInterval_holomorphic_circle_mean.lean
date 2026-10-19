-- Prove2me | solution 1 for Ehrhart.WeightedTorusWeylRepresentativeBridge.polarInterval_holomorphic_circle_mean
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.229985+00:00
-- url     : https://prove2.me/submissions/9e7380e2-5122-42b3-b1fe-8a2a856cb416

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.WeightedTorusWeylRepresentativeBridge
open Set MeasureTheory Filter Complex
open scoped BigOperators ContDiff Convolution ENNReal Topology
open DolbeaultRegularity DolbeaultGraphDistributionBridge
namespace Ehrhart.WeightedTorusWeylRepresentativeBridge
theorem _root_.solution
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (c : ℂ) (r : ℝ) :
    (∫ θ : ℝ in -Real.pi..Real.pi,
      f (circleMap c r θ)) =
      (2 * Real.pi : ℝ) • f c := by
  have hπ : (2 * Real.pi : ℝ) ≠ 0 :=
    ne_of_gt Real.two_pi_pos
  have hshift :
      (∫ θ : ℝ in 0..2 * Real.pi,
        f (circleMap c r (θ + -Real.pi))) =
        ∫ θ : ℝ in -Real.pi..Real.pi,
          f (circleMap c r θ) := by
    have h := intervalIntegral.integral_comp_add_right
      (a := (0 : ℝ)) (b := 2 * Real.pi)
      (fun θ : ℝ => f (circleMap c r θ)) (-Real.pi)
    convert h using 1
    all_goals ring_nf
  have hnormalized :
      (2 * Real.pi : ℝ)⁻¹ •
          (∫ θ : ℝ in -Real.pi..Real.pi,
            f (circleMap c r θ)) = f c := by
    calc
      (2 * Real.pi : ℝ)⁻¹ •
          (∫ θ : ℝ in -Real.pi..Real.pi,
            f (circleMap c r θ)) =
          Real.circleAverage f c r := by
            symm
            calc
              Real.circleAverage f c r =
                  (2 * Real.pi : ℝ)⁻¹ •
                    (∫ θ : ℝ in 0..2 * Real.pi,
                      f (circleMap c r (θ + -Real.pi))) :=
                Real.circleAverage_eq_integral_add (-Real.pi)
              _ = (2 * Real.pi : ℝ)⁻¹ •
                    (∫ θ : ℝ in -Real.pi..Real.pi,
                      f (circleMap c r θ)) := by rw [hshift]
      _ = f c :=
        (hf.diffContOnCl (s := Metric.ball c |r|)).circleAverage
  let A : ℂ :=
    ∫ θ : ℝ in -Real.pi..Real.pi, f (circleMap c r θ)
  have hcancel :
      (2 * Real.pi : ℝ) • ((2 * Real.pi : ℝ)⁻¹ • A) = A := by
    simp only [Complex.real_smul]
    push_cast
    field_simp [Real.pi_ne_zero]
  have h := congrArg
    (fun w : ℂ => (2 * Real.pi : ℝ) • w) hnormalized
  exact hcancel.symm.trans h
end Ehrhart.WeightedTorusWeylRepresentativeBridge
