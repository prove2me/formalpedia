-- Prove2me | solution 1 for AvramDividend.Classical.compensated_jump_exponential_primitive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T20:12:18.217623+00:00
-- url     : https://prove2.me/submissions/1df3bda4-57b2-4023-bc5e-3cba8111ceaa

import Mathlib
open MeasureTheory intervalIntegral

theorem solution (θ z : ℝ) (hθ : 0 < θ) :
    (∫ t in (0 : ℝ)..z, 1 - Real.exp (-θ * t)) =
      (Real.exp (-θ * z) - 1 + θ * z) / θ := by
  have hθ0 : θ ≠ 0 := ne_of_gt hθ
  let F : ℝ → ℝ := fun t => t + Real.exp (-θ * t) / θ
  have hF (x : ℝ) :
      HasDerivAt F (1 - Real.exp (-θ * x)) x := by
    have hlin : HasDerivAt (fun t : ℝ => -θ * t) (-θ) x := by
      simpa only [id_eq, mul_one] using
        ((hasDerivAt_id x).const_mul (-θ))
    have he : HasDerivAt (fun t : ℝ => Real.exp (-θ * t))
        (Real.exp (-θ * x) * (-θ)) x :=
      (Real.hasDerivAt_exp _).comp x hlin
    have hs := (hasDerivAt_id x).add (he.div_const θ)
    have hid : 1 + Real.exp (-θ * x) * (-θ) / θ =
        1 - Real.exp (-θ * x) := by
      field_simp [hθ0]
      ring
    change HasDerivAt F (1 + Real.exp (-θ * x) * (-θ) / θ) x at hs
    rw [hid] at hs
    exact hs
  have hi : IntervalIntegrable
      (fun t : ℝ => 1 - Real.exp (-θ * t)) volume 0 z :=
    (by fun_prop : Continuous
      (fun t : ℝ => 1 - Real.exp (-θ * t))).intervalIntegrable 0 z
  calc
    (∫ t in (0 : ℝ)..z, 1 - Real.exp (-θ * t)) = F z - F 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x _ => hF x) hi
    _ = (Real.exp (-θ * z) - 1 + θ * z) / θ := by
      dsimp [F]
      simp only [mul_zero, neg_zero, Real.exp_zero, zero_add]
      field_simp [hθ0]
      ring
