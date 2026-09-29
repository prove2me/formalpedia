-- Prove2me | solution 1 for Diaz.torsion_dichotomy
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T07:09:56.054304+00:00
-- url     : https://prove2.me/submissions/9d4ab063-b110-44ab-95f0-569d48ab9c47

import Mathlib

open ComplexConjugate

theorem solution (u : ℂ) :
    (∃ q : ℚ, u.im = (q : ℝ) * Real.pi) ↔
      ∃ k : ℕ, 0 < k ∧ ∃ t : ℝ, 0 < t ∧ Complex.exp u ^ k = (t : ℂ) := by
  constructor
  · rintro ⟨q, hq⟩
    have hd0 : ((q.den : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
    have hR : 2 * (q.den : ℝ) * u.im = 2 * (q.num : ℝ) * Real.pi := by
      rw [hq, Rat.cast_def]; field_simp
    refine ⟨2 * q.den, by positivity, Real.exp (2 * (q.den : ℝ) * u.re), Real.exp_pos _, ?_⟩
    rw [← Complex.exp_nat_mul]
    have key : ((2 * q.den : ℕ) : ℂ) * u
        = ((2 * (q.den : ℝ) * u.re : ℝ) : ℂ) + (q.num : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      apply Complex.ext
      · simp
      · simp
        linarith [hR]
    have hone : Complex.exp ((q.num : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) = 1 :=
      Complex.exp_eq_one_iff.mpr ⟨q.num, rfl⟩
    rw [key, Complex.exp_add, hone, mul_one, ← Complex.ofReal_exp]
  · rintro ⟨k, hk, t, ht, hkt⟩
    rw [← Complex.exp_nat_mul] at hkt
    have him : (Complex.exp ((k : ℂ) * u)).im = 0 := by rw [hkt]; simp
    rw [Complex.exp_im] at him
    have hs : Real.sin (((k : ℂ) * u).im) = 0 := by
      rcases mul_eq_zero.mp him with h | h
      · exact absurd h (Real.exp_ne_zero _)
      · exact h
    have hkim : ((k : ℂ) * u).im = (k : ℝ) * u.im := by simp
    rw [hkim] at hs
    obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hs
    have hk0 : ((k : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    refine ⟨(n : ℚ) / (k : ℚ), ?_⟩
    have hcast : (((n : ℚ) / (k : ℚ) : ℚ) : ℝ) = (n : ℝ) / (k : ℝ) := by push_cast; ring
    rw [hcast]
    field_simp
    linarith [hn]
