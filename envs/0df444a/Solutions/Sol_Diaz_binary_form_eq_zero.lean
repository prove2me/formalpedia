-- Prove2me | solution 1 for Diaz.binary_form_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T07:15:39.470574+00:00
-- url     : https://prove2.me/submissions/9cd387c4-0690-4883-a03f-0711d5c49c94

import Mathlib

open ComplexConjugate

theorem aux_powers_indep {K : Subfield ℂ} {u : ℂ} (hT : Transcendental K u) (n : ℕ)
    (k : ℕ → ℂ) (hk : ∀ i, k i ∈ K)
    (h : ∑ i ∈ Finset.range n, k i * u ^ i = 0) :
    ∀ i ∈ Finset.range n, k i = 0 := by
  classical
  set P : Polynomial K :=
    ∑ i ∈ Finset.range n, Polynomial.C (⟨k i, hk i⟩ : K) * Polynomial.X ^ i with hPdef
  have hev : Polynomial.aeval u P = 0 := by
    rw [hPdef]
    simp only [map_sum, map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow]
    rw [← h]
    rfl
  have hP : P = 0 := by
    by_contra hne
    exact hT ⟨P, hne, hev⟩
  intro i hi
  have hc : P.coeff i = 0 := by rw [hP]; simp
  rw [hPdef] at hc
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    mul_ite, mul_one, mul_zero] at hc
  rw [Finset.sum_ite_eq, if_pos hi] at hc
  simpa using congrArg (fun z : K => (z : ℂ)) hc

theorem solution {K : Subfield ℂ} {x y : ℂ} (hy : y ≠ 0)
    (hxy : Transcendental K (x / y)) (d : ℕ) (c : ℕ → ℂ) (hc : ∀ i, c i ∈ K)
    (h : ∑ i ∈ Finset.range (d + 1), c i * x ^ i * y ^ (d - i) = 0) :
    ∀ i ∈ Finset.range (d + 1), c i = 0 := by
  refine aux_powers_indep hxy (d + 1) c hc ?_
  have hyd : (y : ℂ) ^ d ≠ 0 := pow_ne_zero _ hy
  apply mul_left_cancel₀ hyd
  rw [mul_zero, Finset.mul_sum, ← h]
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hle : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [div_pow, pow_sub₀ y hy hle]
  field_simp
