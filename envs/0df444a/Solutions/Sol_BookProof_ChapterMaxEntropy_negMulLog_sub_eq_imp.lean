-- Prove2me | solution 1 for BookProof.ChapterMaxEntropy.negMulLog_sub_eq_imp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:55:19.28798+00:00
-- url     : https://prove2.me/submissions/efc7cd97-bb3a-48e3-8aa8-016aedef4ec7

-- Generated from ChapterMaxEntropy.lean — solution of BookProof.ChapterMaxEntropy.negMulLog_sub_eq_imp
import Mathlib
import Definitions.Def_ChapterMaxEntropy
open BookProof.ChapterMaxEntropy



open Real BigOperators Finset


variable {α : Type*} [Fintype α]

variable {α : Type*} [Fintype α]

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x)
    (heq : Real.negMulLog x - x * Real.log n = (n : ℝ)⁻¹ - x) : x = (n : ℝ)⁻¹ := by

  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rcases eq_or_lt_of_le hx with h | h
  · exfalso
    rw [← h] at heq
    simp [Real.negMulLog] at heq
    have : (0 : ℝ) < (n : ℝ)⁻¹ := by positivity
    linarith [heq]
  · by_contra hne
    have hxn : x * (n : ℝ) ≠ 1 := by
      intro hcontra
      apply hne
      field_simp at hcontra ⊢
      linarith [hcontra]
    have key : Real.negMulLog x - x * Real.log n = x * Real.log ((x * n)⁻¹) := by
      rw [Real.negMulLog, Real.log_inv, Real.log_mul (ne_of_gt h) (ne_of_gt hnR)]; ring
    have hstrict : Real.log ((x * n)⁻¹) < (x * n)⁻¹ - 1 :=
      Real.log_lt_sub_one_of_pos (by positivity) (by
        intro hc
        apply hxn
        field_simp at hc
        linarith [hc])
    have hlt : x * Real.log ((x * n)⁻¹) < x * ((x * n)⁻¹ - 1) :=
      mul_lt_mul_of_pos_left hstrict h
    rw [key] at heq
    have hval : x * ((x * n)⁻¹ - 1) = (n : ℝ)⁻¹ - x := by field_simp
    rw [hval] at hlt
    linarith [heq, hlt]
