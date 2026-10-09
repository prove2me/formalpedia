-- Prove2me | solution 1 for BookProof.ChapterBijectionProbability.bijProb_le_one_div
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T19:28:34.399601+00:00
-- url     : https://prove2.me/submissions/8fc8adb8-dd42-403d-b291-3d5b40f97e2c

-- Generated from ChapterBijectionProbability.lean — solution of BookProof.ChapterBijectionProbability.bijProb_le_one_div
import Mathlib
import Definitions.Def_ChapterBijectionProbability
import Theorems.Thm_BookProof_ChapterBijectionProbability_factorial_succ_le
open BookProof.ChapterBijectionProbability



open scoped Nat
open Filter Asymptotics

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) (hn : 1 ≤ n) : bijProb n ≤ 1 / (n : ℝ) := by

  cases n with
  | zero => omega
  | succ m =>
    have hpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hcast : ((m + 1)! : ℝ) ≤ ((m : ℝ) + 1) ^ m := by
      have := factorial_succ_le m
      calc ((m + 1)! : ℝ) ≤ (((m + 1) ^ m : ℕ) : ℝ) := by exact_mod_cast this
        _ = ((m : ℝ) + 1) ^ m := by push_cast; ring
    simp only [bijProb]
    rw [div_le_div_iff₀ (by push_cast; positivity) (by push_cast; positivity)]
    push_cast
    calc ((m + 1)! : ℝ) * ((m : ℝ) + 1) ≤ ((m : ℝ) + 1) ^ m * ((m : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right hcast (le_of_lt hpos)
      _ = 1 * ((m : ℝ) + 1) ^ (m + 1) := by ring
