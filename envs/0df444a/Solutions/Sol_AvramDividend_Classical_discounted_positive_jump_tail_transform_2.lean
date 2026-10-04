-- Prove2me | solution 2 for AvramDividend.Classical.discounted_positive_jump_tail_transform
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T22:36:09.767984+00:00
-- url     : https://prove2.me/submissions/ec9f133b-48c9-46b7-861e-d56e2cd55cd1

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

theorem c11235d7_expInt (θ z : ℝ) (hθ : 0 < θ) :
    (∫ t in (0 : ℝ)..z, Real.exp (-θ * t)) =
      (1 - Real.exp (-θ * z)) / θ := by
  have hθ0 : θ ≠ 0 := hθ.ne'
  have hd : ∀ x ∈ Set.uIcc (0 : ℝ) z,
      HasDerivAt (fun t => -Real.exp (-θ * t) / θ) (Real.exp (-θ * x)) x := by
    intro x _
    have h1 : HasDerivAt (fun t => -θ * t) (-θ) x := by
      simpa using (hasDerivAt_id x).const_mul (-θ)
    have h2 := ((h1.exp).neg).div_const θ
    exact h2.congr_deriv (by rw [mul_neg, neg_neg, mul_div_assoc, div_self hθ0, mul_one])
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd]
  · simp only [mul_zero, Real.exp_zero]
    field_simp
    ring
  · exact (by fun_prop : Continuous fun t : ℝ => Real.exp (-θ * t)).intervalIntegrable _ _

open MeasureTheory Set NNReal ENNReal in
theorem solution (μ : Measure ℝ≥0) (θ : ℝ) (hθ : 0 < θ) :
    (∫⁻ t in Ioi (0 : ℝ),
       μ {z : ℝ≥0 | t < (z : ℝ)} *
         ENNReal.ofReal (Real.exp (-θ * t))) =
      ∫⁻ z : ℝ≥0,
        ENNReal.ofReal ((1 - Real.exp (-θ * (z : ℝ))) / θ) ∂μ := by
  have h := lintegral_comp_eq_lintegral_meas_lt_mul (f := fun z : ℝ≥0 => (z : ℝ))
    (g := fun t => Real.exp (-θ * t)) μ
    (Filter.Eventually.of_forall fun z => z.2)
    (by fun_prop : Measurable fun z : ℝ≥0 => (z : ℝ)).aemeasurable
    (fun t _ => (by fun_prop : Continuous fun t : ℝ => Real.exp (-θ * t)).intervalIntegrable _ _)
    (Filter.Eventually.of_forall fun t => (Real.exp_pos _).le)
  rw [← h]
  apply lintegral_congr
  intro z
  simp only [c11235d7_expInt θ (z : ℝ) hθ]
