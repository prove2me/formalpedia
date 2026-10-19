-- Prove2me | solution 2 for CohnElkies.poissonLogisticDensity_abs_moment_integrable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:19:43.083902+00:00
-- url     : https://prove2.me/submissions/71711d19-ac1f-4f71-8283-09ced5e7b88f

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
theorem h47_int_abs_pow_exp (n : ℕ) {a : ℝ} (ha : 0 < a) :
    MeasureTheory.Integrable (fun T : ℝ => |T| ^ n * Real.exp (-a * |T|)) := by
  have h1 := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n : ℝ)) (p := 1) (b := a)
    (by have := n.cast_nonneg (α := ℝ); linarith) one_pos ha
  have hIoi : MeasureTheory.IntegrableOn (fun T : ℝ => |T| ^ n * Real.exp (-a * |T|)) (Set.Ioi 0) := by
    refine h1.congr_fun (fun x hx => ?_) measurableSet_Ioi
    have hx0 : (0:ℝ) < x := hx
    simp [abs_of_pos hx0, Real.rpow_natCast]
  have hIio : MeasureTheory.IntegrableOn (fun T : ℝ => |T| ^ n * Real.exp (-a * |T|)) (Set.Iio 0) := by
    have := (show MeasureTheory.IntegrableOn (fun T : ℝ => |T| ^ n * Real.exp (-a * |T|)) (Set.Ioi (-0)) by
      simpa using hIoi).comp_neg_Iio
    simpa [abs_neg] using this
  have hall : MeasureTheory.IntegrableOn (fun T : ℝ => |T| ^ n * Real.exp (-a * |T|)) (Set.Iic 0 ∪ Set.Ioi 0) :=
    ((integrableOn_Iic_iff_integrableOn_Iio (b := (0:ℝ))).mpr hIio).union hIoi
  rw [Set.Iic_union_Ioi, MeasureTheory.integrableOn_univ] at hall
  exact hall

theorem solution (n : ℕ) :
    Integrable
      (fun u : ℝ => poissonLogisticDensity u * |u| ^ n) := by
  have hmaj := (h47_int_abs_pow_exp n Real.pi_pos).const_mul Real.pi
  have hmeas : Measurable (fun u : ℝ => poissonLogisticDensity u * |u| ^ n) := by
    unfold poissonLogisticDensity; fun_prop
  refine hmaj.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun u => ?_)
  have hE := Real.exp_pos (Real.pi * u)
  have hden0 : 0 ≤ poissonLogisticDensity u := by
    unfold poissonLogisticDensity; positivity
  have key : poissonLogisticDensity u ≤ Real.pi * Real.exp (-Real.pi * |u|) := by
    unfold poissonLogisticDensity
    rw [div_le_iff₀ (by positivity)]
    rcases le_total 0 u with hu | hu
    · rw [abs_of_nonneg hu]
      have h1 : Real.exp (-Real.pi * u) * Real.exp (Real.pi * u) = 1 := by
        rw [← Real.exp_add]; ring_nf; simp
      have h2 := Real.exp_pos (-Real.pi * u)
      have : Real.exp (Real.pi * u) ≤ Real.exp (-Real.pi * u) * (1 + Real.exp (Real.pi * u)) ^ 2 := by
        nlinarith
      nlinarith [Real.pi_pos]
    · rw [abs_of_nonpos hu]
      have : Real.exp (-Real.pi * -u) = Real.exp (Real.pi * u) := by ring_nf
      rw [this]
      have : Real.exp (Real.pi * u) ≤ Real.exp (Real.pi * u) * (1 + Real.exp (Real.pi * u)) ^ 2 := by
        have h1 : (1:ℝ) ≤ (1 + Real.exp (Real.pi * u)) ^ 2 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left h1 hE.le]
      nlinarith [Real.pi_pos]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hden0, abs_of_nonneg (by positivity)]
  calc poissonLogisticDensity u * |u| ^ n ≤ Real.pi * Real.exp (-Real.pi * |u|) * |u| ^ n :=
        mul_le_mul_of_nonneg_right key (by positivity)
    _ = Real.pi * (|u| ^ n * Real.exp (-Real.pi * |u|)) := by ring

