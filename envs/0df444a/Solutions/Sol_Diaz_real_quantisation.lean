-- Prove2me | solution 1 for Diaz.real_quantisation
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T07:08:38.788476+00:00
-- url     : https://prove2.me/submissions/6a313c32-29ca-4a7e-93ef-c45703a00cf4

import Mathlib

open ComplexConjugate

theorem solution {u : ℂ} (hexp : (Complex.exp u).im = 0)
    (hre : u.re ≠ 0) (him : u.im ≠ 0) :
    (∃ n : ℤ, u.im = n * Real.pi) ∧ Real.pi ^ 2 < Complex.normSq u := by
  have hs : Real.sin u.im = 0 := by
    have hx := Complex.exp_im u
    rw [hexp] at hx
    rcases mul_eq_zero.mp hx.symm with h | h
    · exact absurd h (Real.exp_ne_zero _)
    · exact h
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hs
  refine ⟨⟨n, hn.symm⟩, ?_⟩
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn; exact him hn.symm
  have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by
    have : (1 : ℤ) ≤ |n| := Int.one_le_abs (by omega)
    exact_mod_cast this
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have habs : Real.pi ≤ |u.im| := by
    rw [← hn, abs_mul, abs_of_pos hpi]
    nlinarith [abs_nonneg ((n : ℝ))]
  have hsq : Real.pi ^ 2 ≤ u.im ^ 2 := by
    have := sq_abs u.im
    nlinarith [abs_nonneg u.im]
  have hre2 : 0 < u.re ^ 2 := by positivity
  rw [Complex.normSq_apply]
  nlinarith
