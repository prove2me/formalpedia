-- Prove2me | solution 1 for AvramDividend.Classical.discounted_interval_exp_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-03T22:02:40.018983+00:00
-- url     : https://prove2.me/submissions/deb6594b-db9e-41b3-8505-5d0c62cc3067

import Mathlib

open MeasureTheory Set
open scoped NNReal ENNReal

theorem solution (θ z : ℝ) (hθ : 0 < θ) :
    (∫ t in (0 : ℝ)..z, Real.exp (-θ * t)) =
      (1 - Real.exp (-θ * z)) / θ := by
  have hn : θ ≠ 0 := ne_of_gt hθ
  let a : ℝ := -θ
  have ha : a ≠ 0 := by dsimp [a]; exact neg_ne_zero.mpr hn
  have hderiv (t : ℝ) :
      HasDerivAt (fun u : ℝ => a⁻¹ * Real.exp (a * u))
        (Real.exp (a * t)) t := by
    have hlin : HasDerivAt (fun u : ℝ => a * u) a t := by
      simpa using (hasDerivAt_id t).const_mul a
    have he := (hlin.exp).const_mul a⁻¹
    have heq : a⁻¹ * (Real.exp (a * t) * a) = Real.exp (a * t) := by
      calc
        a⁻¹ * (Real.exp (a * t) * a) =
            (a⁻¹ * a) * Real.exp (a * t) := by ring
        _ = Real.exp (a * t) := by simp [ha]
    simpa only [heq] using he
  calc
    (∫ t in (0 : ℝ)..z, Real.exp (-θ * t)) =
        a⁻¹ * Real.exp (a * z) -
          a⁻¹ * Real.exp (a * 0) := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro t ht
        simpa [a] using hderiv t
      · exact (by fun_prop : Continuous (fun t : ℝ => Real.exp (-θ * t))).intervalIntegrable 0 z
    _ = (1 - Real.exp (-θ * z)) / θ := by
      dsimp [a]
      rw [mul_zero, Real.exp_zero]
      field_simp
      ring
