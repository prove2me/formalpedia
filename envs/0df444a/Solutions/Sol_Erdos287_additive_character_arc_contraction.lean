-- Prove2me | solution 1 for Erdos287.additive_character_arc_contraction
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T13:09:54.405866+00:00
-- url     : https://prove2.me/submissions/1a47fae9-7ee5-4993-882d-177c7993f2f2

import Mathlib

set_option autoImplicit false

/-- The standard additive character contracts the binary subset-sum factor
at least quadratically in the distance of its phase from an integer. -/
theorem solution (q : ℕ) [NeZero q] (x : ZMod q) :
    ‖(1 : ℂ) + ZMod.stdAddChar x‖ ≤
      2 * Real.exp (-2 * (min ((x.val : ℝ) / q) (1 - (x.val : ℝ) / q)) ^ 2) := by
  let r := (x.val : ℝ) / q
  let d := min r (1 - r)
  change ‖(1 : ℂ) + ZMod.stdAddChar x‖ ≤ 2 * Real.exp (-2 * d ^ 2)
  have hq : 0 < (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : r ≤ 1 := (div_le_iff₀ hq).mpr (by
    simpa using (show (x.val : ℝ) ≤ q by exact_mod_cast (ZMod.val_lt x).le))
  have hd0 : 0 ≤ d := le_min hr0 (sub_nonneg.mpr hr1)
  have hd1 : d ≤ 1 / 2 := by
    have h₁ : d ≤ r := min_le_left _ _
    have h₂ : d ≤ 1 - r := min_le_right _ _
    linarith
  have hsin : Real.sin (Real.pi * r) = Real.sin (Real.pi * d) := by
    rcases le_total r (1 - r) with h | h
    · rw [show d = r from min_eq_left h]
    · rw [show d = 1 - r from min_eq_right h, mul_sub, mul_one, Real.sin_pi_sub]
  have hbound := Real.mul_le_sin (x := Real.pi * d) (mul_nonneg Real.pi_pos.le hd0)
    (by nlinarith [mul_le_mul_of_nonneg_left hd1 Real.pi_pos.le])
  have hlinear : 2 * d ≤ Real.sin (Real.pi * d) := by
    convert hbound using 1
    field_simp [Real.pi_ne_zero]
  have hre : (ZMod.stdAddChar x).re = Real.cos (2 * (Real.pi * r)) := by
    rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
    have he : 2 * ↑Real.pi * Complex.I * ↑x.val / ↑q =
        (↑(2 * (Real.pi * r)) : ℂ) * Complex.I := by
      dsimp [r]
      push_cast
      ring
    rw [he, Complex.exp_re]
    simp
  have hn : Complex.normSq (ZMod.stdAddChar x) = 1 := by
    rw [ZMod.stdAddChar_apply]
    exact Circle.normSq_coe _
  apply le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (by positivity)
  calc
    ‖(1 : ℂ) + ZMod.stdAddChar x‖ ^ 2 =
        4 * (1 - Real.sin (Real.pi * d) ^ 2) := by
      rw [← Complex.normSq_eq_norm_sq, add_comm, Complex.normSq_add,
        Complex.normSq_one, hn, map_one, mul_one, hre, Real.cos_two_mul_eq_one_sub, hsin]
      ring
    _ ≤ 4 * (1 - 4 * d ^ 2) := by
      have hnonneg : 0 ≤ 2 * d := by positivity
      have hsquare := (sq_le_sq₀ hnonneg (hnonneg.trans hlinear)).mpr hlinear
      nlinarith
    _ ≤ 4 * Real.exp (-4 * d ^ 2) := by linarith [Real.add_one_le_exp (-4 * d ^ 2)]
    _ = (2 * Real.exp (-2 * d ^ 2)) ^ 2 := by
      rw [mul_pow, ← Real.exp_nat_mul]
      norm_num
      ring_nf

