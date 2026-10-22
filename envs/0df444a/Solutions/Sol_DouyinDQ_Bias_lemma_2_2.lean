-- Prove2me | solution 2 for DouyinDQ.Bias.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:28:02.21418+00:00
-- url     : https://prove2.me/submissions/4da9f4bf-f797-4c39-b611-63489ee1c1a9

import Mathlib
set_option autoImplicit false

theorem solution {ι : Type} [Fintype ι] [DecidableEq ι]
    (A A' : Matrix ι ι ℝ)
    (hA : IsUnit (1 - A).det) (hA' : IsUnit (1 - A').det) (K : ℕ) :
    (1 - A')⁻¹ = (1 - A)⁻¹ *
      (∑ k ∈ Finset.range (K + 1), ((A' - A) * (1 - A)⁻¹) ^ k) +
      (1 - A')⁻¹ * ((A' - A) * (1 - A)⁻¹) ^ (K + 1) := by
  set N := (1 - A)⁻¹ with hN
  set P := (1 - A')⁻¹ with hP
  set B := (A' - A) * N with hB
  have h1 : N * (1 - A) = 1 := Matrix.nonsing_inv_mul _ hA
  have h2 : (1 - A) * N = 1 := Matrix.mul_nonsing_inv _ hA
  have h3 : P * (1 - A') = 1 := Matrix.nonsing_inv_mul _ hA'
  have hBA : B * (1 - A) = A' - A := by
    rw [hB, Matrix.mul_assoc, h1, Matrix.mul_one]
  have hfac : (1 - B) * (1 - A) = 1 - A' := by
    rw [Matrix.sub_mul, Matrix.one_mul, hBA]; abel
  have hPB : P * (1 - B) = N := by
    have : P * (1 - B) * (1 - A) = 1 := by rw [Matrix.mul_assoc, hfac, h3]
    calc P * (1 - B) = P * (1 - B) * ((1 - A) * N) := by rw [h2, Matrix.mul_one]
      _ = N := by rw [← Matrix.mul_assoc, this, Matrix.one_mul]
  have step : ∀ k : ℕ, P * B ^ k = N * B ^ k + P * B ^ (k + 1) := by
    intro k
    have h : P * (1 - B) * B ^ k = P * B ^ k - P * B ^ (k + 1) := by
      simp [Matrix.mul_sub, Matrix.sub_mul, pow_succ', Matrix.mul_assoc]
    rw [hPB] at h
    rw [h]; abel
  have main : ∀ K : ℕ, P = N * (∑ k ∈ Finset.range K, B ^ k) + P * B ^ K := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rw [Finset.sum_range_succ, Matrix.mul_add, add_assoc, ← step K]
      exact ih
  exact main (K + 1)
