-- Prove2me | solution 1 for BookProof.ChapterF2.mass_gap
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:58:40.165564+00:00
-- url     : https://prove2.me/submissions/42d97f72-4bd0-4f65-b9af-4664f5ea1c12

-- Generated from ChapterF2.lean — solution of BookProof.ChapterF2.mass_gap
import Mathlib
import Definitions.Def_ChapterF2
import Theorems.Thm_BookProof_ChapterF2_bargmann_self_re
import Theorems.Thm_BookProof_ChapterF2_bargmann_numberOp_re
open BookProof.ChapterF2



open Polynomial Finset
open scoped BigOperators


open BookProof.ChapterF1

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (ψ : ℂ[X]) (hψ : ψ.coeff 0 = 0) :
    (bargmann ψ ψ).re ≤ (bargmann ψ (numberOp ψ)).re := by

  rw [bargmann_self_re, bargmann_numberOp_re]
  apply Finset.sum_le_sum
  intro n hn
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp only [Polynomial.mem_support_iff] at hn; exact absurd hψ hn
    · exact h
  have hnn : (n.factorial : ℝ) ≤ (n : ℝ) * n.factorial := by
    nlinarith [Nat.factorial_pos n, (by exact_mod_cast hn1 : (1 : ℝ) ≤ n)]
  exact mul_le_mul_of_nonneg_right hnn (Complex.normSq_nonneg _)
