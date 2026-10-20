-- Prove2me | solution 2 for CohnElkies.harmonic_stripPoissonExponentialMajorant_abs_integrable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:30:24.072378+00:00
-- url     : https://prove2.me/submissions/94ee999c-6d8d-460b-8a00-e9f47effa0f5

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Asymptotics Bornology Complex Filter Function MeasureTheory Metric Set
open scoped Filter FourierTransform Real SchwartzMap Topology


theorem solution :
    Integrable
      (fun T : ℝ =>
        stripPoissonExponentialMajorant T * |T|) := by
  set c : ℝ := Real.pi / 2 with hcdef
  have hc : 0 < c := by positivity
  set A : ℝ := 1 / c + 27 / c ^ 3 with hA
  refine ((integrable_inv_one_add_sq).const_mul (c * A)).mono'
    (by unfold stripPoissonExponentialMajorant; exact (by fun_prop : Continuous fun T : ℝ =>
      Real.pi / 2 * Real.exp (-(Real.pi / 2) * |T|) * |T|).aestronglyMeasurable)
    (Eventually.of_forall fun T => ?_)
  unfold stripPoissonExponentialMajorant
  have hx : 0 ≤ |T| := abs_nonneg T
  set x := |T| with hxdef
  have hT2 : T ^ 2 = x ^ 2 := (sq_abs T).symm
  set E := Real.exp (c * x) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hneg : Real.exp (-c * x) = E⁻¹ := by
    rw [hE, ← Real.exp_neg]; congr 1; ring
  have e1 : c * x ≤ E := by linarith [Real.add_one_le_exp (c * x)]
  have e3 : (c * x) ^ 3 ≤ 27 * E := by
    have h1 : c * x / 3 ≤ Real.exp (c * x / 3) := by linarith [Real.add_one_le_exp (c * x / 3)]
    have h2 : E = Real.exp (c * x / 3) ^ 3 := by
      rw [hE, ← Real.exp_nat_mul]; congr 1; push_cast; ring
    have h3 : (c * x / 3) ^ 3 ≤ Real.exp (c * x / 3) ^ 3 :=
      pow_le_pow_left₀ (by positivity) h1 3
    rw [h2]; nlinarith [h3]
  have k1 : x ≤ E / c := by rw [le_div_iff₀ hc]; linarith
  have k3 : x ^ 3 ≤ 27 * E / c ^ 3 := by
    rw [le_div_iff₀ (by positivity)]; nlinarith [mul_pow c x 3]
  have key : x * (1 + x ^ 2) ≤ A * E := by
    have : A * E = E / c + 27 * E / c ^ 3 := by rw [hA]; ring
    nlinarith
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hneg, hT2]
  rw [show c * A * (1 + x ^ 2)⁻¹ = c * A / (1 + x ^ 2) by ring, le_div_iff₀ (by positivity)]
  have : c * E⁻¹ * x * (1 + x ^ 2) = c * E⁻¹ * (x * (1 + x ^ 2)) := by ring
  rw [this]
  calc c * E⁻¹ * (x * (1 + x ^ 2)) ≤ c * E⁻¹ * (A * E) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = c * A := by field_simp

