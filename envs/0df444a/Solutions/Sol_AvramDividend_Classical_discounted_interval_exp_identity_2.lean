-- Prove2me | solution 2 for AvramDividend.Classical.discounted_interval_exp_identity
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T22:21:06.869983+00:00
-- url     : https://prove2.me/submissions/a37599b8-4002-496a-84f4-9d05c3cac93b

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

theorem solution (θ z : ℝ) (hθ : 0 < θ) :
    (∫ t in (0 : ℝ)..z, Real.exp (-θ * t)) =
      (1 - Real.exp (-θ * z)) / θ := by
  have hθ0 : θ ≠ 0 := hθ.ne'
  have hd : ∀ x ∈ Set.uIcc (0 : ℝ) z,
      HasDerivAt (fun t => -Real.exp (-θ * t) / θ) (Real.exp (-θ * x)) x := by
    intro x _
    have h1 : HasDerivAt (fun t => -θ * t) (-θ) x := by
      simpa using (hasDerivAt_id x).const_mul (-θ)
    have h2 : HasDerivAt (fun t => -Real.exp (-θ * t) / θ)
        (-(Real.exp (-θ * x) * -θ) / θ) x := ((h1.exp).neg).div_const θ
    have h3 : -(Real.exp (-θ * x) * -θ) / θ = Real.exp (-θ * x) := by
      rw [div_eq_iff hθ0]
      ring
    rwa [h3] at h2
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd]
  · simp only [mul_zero, Real.exp_zero]
    field_simp
    ring
  · exact (by fun_prop : Continuous fun t : ℝ => Real.exp (-θ * t)).intervalIntegrable _ _
