-- Prove2me | solution 2 for CohnElkies.stripPoissonExponentialMajorant_mul_lowerEndpointPhase_integrable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:44:34.186984+00:00
-- url     : https://prove2.me/submissions/a964e3c0-1686-46af-a815-008ba29431ff

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

theorem solution :
    Integrable
      (fun T : ℝ =>
        stripPoissonExponentialMajorant T *
          ‖lowerEndpointPhase T‖) := by
  have hpi := Real.pi_pos
  have hmaj : Integrable (fun T : ℝ => Real.pi / 2 * (Real.pi / 2) *
      (|T| ^ 1 * Real.exp (-(Real.pi / 2) * |T|)) + Real.pi / 2 / 8 *
      (|T| ^ 2 * Real.exp (-(Real.pi / 2) * |T|))) :=
    ((h47_int_abs_pow_exp 1 (by positivity)).const_mul _).add
      ((h47_int_abs_pow_exp 2 (by positivity)).const_mul _)
  have hmeas : Measurable (fun T : ℝ => stripPoissonExponentialMajorant T * ‖lowerEndpointPhase T‖) := by
    unfold stripPoissonExponentialMajorant lowerEndpointPhase
    fun_prop
  refine hmaj.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun T => ?_)
  have hT := abs_nonneg T
  have hph : |lowerEndpointPhase T| ≤ Real.pi / 2 * |T| + T ^ 2 / 8 := by
    unfold lowerEndpointPhase
    have hl0 : 0 ≤ Real.log (1 + T ^ 2 / 4) := Real.log_nonneg (by nlinarith [sq_nonneg T])
    have hl1 : Real.log (1 + T ^ 2 / 4) ≤ T ^ 2 / 4 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + T ^ 2 / 4 by positivity); linarith
    have ha0 : 0 ≤ Real.arctan (|T| / 2) := Real.arctan_nonneg.mpr (by positivity)
    have ha1 : Real.arctan (|T| / 2) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have hprod : |T| / 2 * Real.arctan (|T| / 2) ≤ |T| / 2 * (Real.pi / 2) :=
      mul_le_mul_of_nonneg_left ha1.le (by positivity)
    have hprod0 : 0 ≤ |T| / 2 * Real.arctan (|T| / 2) := by positivity
    rw [abs_le]; constructor <;> nlinarith
  have hE := Real.exp_pos (-(Real.pi / 2) * |T|)
  unfold stripPoissonExponentialMajorant
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_abs, abs_of_pos (by positivity)]
  calc Real.pi / 2 * Real.exp (-(Real.pi / 2) * |T|) * |lowerEndpointPhase T|
      ≤ Real.pi / 2 * Real.exp (-(Real.pi / 2) * |T|) * (Real.pi / 2 * |T| + T ^ 2 / 8) :=
        mul_le_mul_of_nonneg_left hph (by positivity)
    _ = _ := by rw [← sq_abs T]; ring

