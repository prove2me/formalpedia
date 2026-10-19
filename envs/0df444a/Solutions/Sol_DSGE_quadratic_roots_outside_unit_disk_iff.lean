-- Prove2me | solution 1 for DSGE.quadratic_roots_outside_unit_disk_iff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T05:29:24.86328+00:00
-- url     : https://prove2.me/submissions/bf327b6b-c3c6-46dc-8e99-1e9bced1dde8

import Mathlib

namespace DSGEQ

lemma real_root_bound (T D x : ℝ) (hD1 : 1 < D) (hT : |T| < 1 + D)
    (hx : x ^ 2 - T * x + D = 0) : 1 < |x| := by
  by_contra h
  push Not at h
  have h1 : x ^ 2 + D = T * x := by linarith
  have h2 : T * x ≤ |T| * |x| := by
    calc T * x ≤ |T * x| := le_abs_self _
      _ = |T| * |x| := abs_mul _ _
  have h3 : |x| ^ 2 = x ^ 2 := sq_abs x
  have h4 : 0 ≤ |x| := abs_nonneg x
  have h5 : |T| * |x| ≤ (1 + D) * |x| := mul_le_mul_of_nonneg_right hT.le h4
  -- (|x| - 1)(|x| - D) ≤ 0 would need ... derive contradiction
  have h6 : |x| ^ 2 - (1 + D) * |x| + D ≤ 0 := by nlinarith
  have h7 : 0 < (1 - |x|) * (D - |x|) ∨ |x| = 1 := by
    rcases lt_or_eq_of_le h with h | h
    · left; apply mul_pos <;> linarith
    · right; exact h
  rcases h7 with h7 | h7
  · nlinarith
  · -- |x| = 1 : then |T| * 1 ≥ 1 + D, contradiction
    have : |T| * |x| ≥ x ^ 2 + D := by linarith
    rw [h7] at this; nlinarith [sq_abs x]

end DSGEQ

open DSGEQ in
theorem solution (T D : ℝ) (hD : 0 < D) :
    (∀ z : ℂ, z ^ 2 - (T : ℂ) * z + (D : ℂ) = 0 → 1 < ‖z‖) ↔ 1 < D ∧ |T| < 1 + D := by
  constructor
  · intro h
    by_cases hdisc : T ^ 2 < 4 * D
    · -- complex conjugate roots of modulus √D
      set y := √(D - T ^ 2 / 4) with hy
      have hy2 : y ^ 2 = D - T ^ 2 / 4 := Real.sq_sqrt (by nlinarith)
      have hz := h ⟨T / 2, y⟩ (by
        apply Complex.ext <;> simp [pow_two] <;> nlinarith [hy2])
      have hn : ‖(⟨T / 2, y⟩ : ℂ)‖ ^ 2 = D := by
        rw [Complex.sq_norm, Complex.normSq_mk]; nlinarith [hy2]
      have hD1 : 1 < D := by nlinarith [norm_nonneg (⟨T / 2, y⟩ : ℂ)]
      refine ⟨hD1, ?_⟩
      have hs : √D ^ 2 = D := Real.sq_sqrt hD.le
      have hT2 : |T| < 2 * √D := by
        rw [← sq_lt_sq₀ (abs_nonneg T) (by positivity), sq_abs, mul_pow, hs]; linarith
      nlinarith [sq_nonneg (√D - 1)]
    · push Not at hdisc
      set q := √(T ^ 2 - 4 * D) with hq
      have hq2 : q ^ 2 = T ^ 2 - 4 * D := Real.sq_sqrt (by linarith)
      set a := (T + q) / 2
      set b := (T - q) / 2
      have hab : a * b = D := by simp only [a, b]; nlinarith [hq2]
      have hapb : a + b = T := by simp only [a, b]; ring
      have ha : 1 < |a| := by
        have := h (a : ℂ) (by
          have : a ^ 2 - T * a + D = 0 := by rw [← hapb, ← hab]; ring
          exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) this)
        simpa using this
      have hb : 1 < |b| := by
        have := h (b : ℂ) (by
          have : b ^ 2 - T * b + D = 0 := by rw [← hapb, ← hab]; ring
          exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) this)
        simpa using this
      have hD1 : 1 < D := by
        rw [← hab, ← abs_of_pos (hab ▸ hD : 0 < a * b), abs_mul]; nlinarith [abs_nonneg a]
      refine ⟨hD1, ?_⟩
      have hsign : (0 < a ∧ 0 < b) ∨ (a < 0 ∧ b < 0) := by
        rcases lt_or_gt_of_ne (show a ≠ 0 by rintro h0; simp [h0] at ha; linarith) with h1 | h1 <;>
        rcases lt_or_gt_of_ne (show b ≠ 0 by rintro h0; simp [h0] at hb; linarith) with h2 | h2
        · right; exact ⟨h1, h2⟩
        · nlinarith [mul_neg_of_neg_of_pos h1 h2]
        · nlinarith [mul_neg_of_pos_of_neg h1 h2]
        · left; exact ⟨h1, h2⟩
      rw [abs_lt]
      rcases hsign with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [abs_of_pos h1] at ha; rw [abs_of_pos h2] at hb
        constructor <;> nlinarith
      · rw [abs_of_neg h1] at ha; rw [abs_of_neg h2] at hb
        constructor <;> nlinarith
  · rintro ⟨hD1, hT⟩ z hz
    have hre := congrArg Complex.re hz
    have him := congrArg Complex.im hz
    simp [pow_two] at hre him
    by_cases hy : z.im = 0
    · have hx : z.re ^ 2 - T * z.re + D = 0 := by rw [hy] at hre; nlinarith
      have := real_root_bound T D z.re hD1 hT hx
      have hz' : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [hy])
      rw [hz']; simpa using this
    · have hx : z.re = T / 2 := by
        have : z.im * (2 * z.re - T) = 0 := by nlinarith
        rcases mul_eq_zero.mp this with h | h
        · exact absurd h hy
        · linarith
      have hn : ‖z‖ ^ 2 = D := by
        have him2 : z.im * z.im = D - T ^ 2 / 4 := by rw [hx] at hre; linarith
        rw [Complex.sq_norm, Complex.normSq_apply, him2, hx]; ring
      nlinarith [norm_nonneg z]
