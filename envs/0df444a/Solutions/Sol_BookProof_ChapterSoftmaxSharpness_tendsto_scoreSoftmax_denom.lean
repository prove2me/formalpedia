-- Prove2me | solution 1 for BookProof.ChapterSoftmaxSharpness.tendsto_scoreSoftmax_denom
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:43:44.718506+00:00
-- url     : https://prove2.me/submissions/b11da4d8-563e-4d1e-9a75-4f2f1d1797a7

-- Generated from ChapterSoftmaxSharpness.lean — solution of BookProof.ChapterSoftmaxSharpness.tendsto_scoreSoftmax_denom
import Mathlib
import Definitions.Def_ChapterSoftmaxSharpness
import Theorems.Thm_BookProof_ChapterSoftmaxSharpness_tendsto_exp_mul_neg
import Definitions.Def_ChapterSoftmaxBorn
open BookProof.ChapterSoftmaxSharpness



open scoped BigOperators

noncomputable section


open Filter Topology BookProof.ChapterSoftmaxBorn

variable {n m : ℕ}

variable {n m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (s : Fin m → ℝ) (j : Fin m)
    (hmax : ∀ l, l ≠ j → s l < s j) :
    Tendsto (fun b : ℝ => ∑ l, Real.exp (b * (s l - s j))) atTop (𝓝 1) := by

  have h : Tendsto (fun b : ℝ => ∑ l, Real.exp (b * (s l - s j))) atTop
      (𝓝 (∑ l : Fin m, if l = j then (1 : ℝ) else 0)) := by
    refine tendsto_finset_sum _ fun l _ => ?_
    by_cases hl : l = j
    · subst hl
      simp
    · simpa [hl] using tendsto_exp_mul_neg (s l - s j) (by linarith [hmax l hl])
  simpa using h
