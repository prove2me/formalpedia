-- Prove2me | solution 1 for DouyinDQ.Bias.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T16:19:42.759439+00:00
-- url     : https://prove2.me/submissions/71c19268-51e8-46b9-ad1e-182e5b027a1a

import Mathlib

theorem solution {ι : Type} [Fintype ι] [DecidableEq ι]
    (A A' : Matrix ι ι ℝ)
    (hA : IsUnit (1 - A).det) (hA' : IsUnit (1 - A').det) (K : ℕ) :
    (1 - A')⁻¹ = (1 - A)⁻¹ *
      (∑ k ∈ Finset.range (K + 1), ((A' - A) * (1 - A)⁻¹) ^ k) +
      (1 - A')⁻¹ * ((A' - A) * (1 - A)⁻¹) ^ (K + 1) := by
  set B := (1 - A)⁻¹ with hB
  set C := (1 - A')⁻¹ with hC
  set X := (A' - A) * B with hX
  have hCl : C * (1 - A') = 1 := Matrix.nonsing_inv_mul _ hA'
  have hBr : (1 - A) * B = 1 := Matrix.mul_nonsing_inv _ hA
  have key : C = B + C * X := by
    have e1 : B = C * (1 - A') * B := by rw [hCl, one_mul]
    calc C = C * ((1 - A) * B) := by rw [hBr, mul_one]
      _ = C * (1 - A') * B + C * X := by
        rw [hX]; simp only [Matrix.mul_assoc, ← Matrix.mul_add, ← Matrix.add_mul]; congr 2; abel
      _ = B + C * X := by rw [← e1]
  induction K with
  | zero => simpa using key
  | succ K ih =>
    rw [Finset.sum_range_succ, Matrix.mul_add, add_assoc]
    conv_lhs => rw [ih]
    congr 1
    conv_lhs => rw [key]
    rw [Matrix.add_mul, Matrix.mul_assoc, ← pow_succ']
