-- Prove2me | solution 1 for Diaz.order_quantisation
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T07:10:42.575227+00:00
-- url     : https://prove2.me/submissions/32b58ff3-9c2b-4502-965d-5e766df8d41c

import Mathlib

open ComplexConjugate

theorem solution {u : ℂ} {m : ℕ} (hm : 0 < m)
    (hξ : (Complex.exp u / conj (Complex.exp u)) ^ m = 1)
    (hre : u.re ≠ 0) (him : u.im ≠ 0) :
    Real.pi ^ 2 / (m : ℝ) ^ 2 < Complex.normSq u := by
  have hconj : conj (Complex.exp u) = Complex.exp (conj u) := (Complex.exp_conj u).symm
  rw [hconj, ← Complex.exp_sub, ← Complex.exp_nat_mul] at hξ
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hξ
  rw [Complex.sub_conj] at hn
  have hIne : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  have h2 : ((m : ℂ) * (((2 * u.im : ℝ)) : ℂ)) * Complex.I
      = ((n : ℂ) * (2 * (Real.pi : ℂ))) * Complex.I := by linear_combination hn
  have h3 := mul_right_cancel₀ hIne h2
  have hnR : (m : ℝ) * u.im = (n : ℝ) * Real.pi := by
    have hcc : ((((m : ℝ)) * u.im : ℝ) : ℂ) = ((((n : ℝ)) * Real.pi : ℝ) : ℂ) := by
      push_cast at h3 ⊢; linear_combination h3 / 2
    exact_mod_cast hcc
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp only [Int.cast_zero, zero_mul] at hnR
    rcases mul_eq_zero.mp hnR with h | h
    · exact absurd h (ne_of_gt hm0)
    · exact him h
  have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by
    have : (1 : ℤ) ≤ |n| := Int.one_le_abs (by omega)
    exact_mod_cast this
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have habs : Real.pi / (m : ℝ) ≤ |u.im| := by
    have hmul : (m : ℝ) * |u.im| = |(n : ℝ)| * Real.pi := by
      rw [← abs_of_pos hm0, ← abs_mul, hnR, abs_mul, abs_of_pos hpi]
    rw [div_le_iff₀ hm0, mul_comm]
    nlinarith
  have hsq : (Real.pi / (m : ℝ)) ^ 2 ≤ u.im ^ 2 := by
    have h0 : (0 : ℝ) ≤ Real.pi / (m : ℝ) := by positivity
    nlinarith [sq_abs u.im, abs_nonneg u.im]
  have hre2 : 0 < u.re ^ 2 := by positivity
  have hdp : Real.pi ^ 2 / (m : ℝ) ^ 2 = (Real.pi / (m : ℝ)) ^ 2 := (div_pow _ _ 2).symm
  rw [hdp, Complex.normSq_apply]
  nlinarith
