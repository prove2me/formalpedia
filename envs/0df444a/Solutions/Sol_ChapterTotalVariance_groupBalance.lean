-- Prove2me | solution 1 for ChapterTotalVariance.groupBalance
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:34:06.021048+00:00
-- url     : https://prove2.me/submissions/dfee2006-975d-4dc0-9c39-45b813bf5aed

-- Generated from ChapterTotalVariance.lean — solution of ChapterTotalVariance.groupBalance
import Mathlib
import Definitions.Def_ChapterTotalVariance
import Definitions.Def_ChapterA4
open ChapterTotalVariance




open scoped BigOperators
open Finset

variable {Ω κ : Type*} [Fintype Ω] [DecidableEq κ]

variable {Ω κ : Type*} [Fintype Ω] [DecidableEq κ]

set_option maxHeartbeats 1000000 in
theorem solution (w : Ω → ℝ) (X : Ω → κ) (Y : Ω → ℝ)
    (hw : ∀ ω, 0 ≤ w ω) (g : κ) :
    (∑ ω, if X ω = g then w ω * (Y ω - condMean w X Y g) else 0) = 0 := by

  -- Let `N = ∑ (if X ω = g then w ω * Y ω else 0)` and `P = groupProb w X g`.
  -- Distribute: the sum equals `N - condMean·P = N - (N / P)·P`.
  -- If `P ≠ 0`, `(N/P)·P = N` so the result is `0`.
  -- If `P = 0`, then `condMean = N/0 = 0`; and since `P = ∑ (if X ω = g then w ω else 0)`
  -- is a sum of nonnegatives equal to `0`, every `w ω` with `X ω = g` is `0`, hence `N = 0`.
  simp only [condMean]
  set P : ℝ := groupProb w X g with hP
  set N : ℝ := ∑ ω, if X ω = g then w ω * Y ω else 0 with hN
  have hdist : (∑ ω, if X ω = g then w ω * (Y ω - N / P) else 0) = N - (N / P) * P := by
    rw [hN, hP, groupProb, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun ω _ => ?_)
    by_cases h : X ω = g
    · simp only [h, if_true]; ring
    · simp only [h, if_false, sub_zero, mul_zero]
  rw [hdist]
  by_cases hP0 : P = 0
  · have hNz : N = 0 := by
      have hnn : ∀ ω ∈ Finset.univ, (0 : ℝ) ≤ if X ω = g then w ω else 0 := by
        intro ω _; by_cases h : X ω = g <;> simp [h, hw ω]
      have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 (by rw [← groupProb]; exact hP0)
      rw [hN]; refine Finset.sum_eq_zero (fun ω _ => ?_)
      by_cases h : X ω = g
      · have : w ω = 0 := by have := hz ω (Finset.mem_univ ω); simpa [h] using this
        simp [h, this]
      · simp [h]
    rw [hNz, hP0]; ring
  · rw [div_mul_cancel₀ N hP0, sub_self]
