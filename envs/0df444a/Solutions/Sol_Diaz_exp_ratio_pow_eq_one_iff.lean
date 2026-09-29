-- Prove2me | solution 1 for Diaz.exp_ratio_pow_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T11:01:34.32746+00:00
-- url     : https://prove2.me/submissions/6f2f48f8-ce23-401f-be73-aac42f157721

import Mathlib

open ComplexConjugate

theorem solution (v : ℂ) (m : ℕ) :
    (Complex.exp v / conj (Complex.exp v)) ^ m = 1
      ↔ ∃ n : ℤ, (m : ℝ) * v.im = (n : ℝ) * Real.pi := by
  have hsub : v - conj v = ((2 * v.im : ℝ) : ℂ) * Complex.I := by
    refine Complex.ext ?_ ?_
    · simp
    · simp
      ring
  have h2 : (Complex.exp v / conj (Complex.exp v)) ^ m
      = Complex.exp ((m : ℂ) * (v - conj v)) := by
    rw [← Complex.exp_conj, ← Complex.exp_sub, ← Complex.exp_nat_mul]
  rw [h2, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [hsub] at hn
    have := congrArg Complex.im hn
    simp at this
    linarith
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [hsub]
    refine Complex.ext ?_ ?_
    · simp
    · simp
      linarith
