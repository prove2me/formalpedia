-- Prove2me | solution 1 for BookProof.ChapterSoftmaxSharpness.tendsto_scoreSoftmax_ne
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:43:46.777679+00:00
-- url     : https://prove2.me/submissions/79e1f659-b826-433f-aeca-da1643648d31

-- Generated from ChapterSoftmaxSharpness.lean — solution of BookProof.ChapterSoftmaxSharpness.tendsto_scoreSoftmax_ne
import Mathlib
import Definitions.Def_ChapterSoftmaxSharpness
import Theorems.Thm_BookProof_ChapterSoftmaxSharpness_tendsto_exp_mul_neg
import Theorems.Thm_BookProof_ChapterSoftmaxSharpness_tendsto_scoreSoftmax_denom
import Definitions.Def_ChapterSoftmaxBorn
open BookProof.ChapterSoftmaxSharpness



open scoped BigOperators

noncomputable section


open Filter Topology BookProof.ChapterSoftmaxBorn

variable {n m : ℕ}

variable {n m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (s : Fin m → ℝ) (j i : Fin m)
    (hmax : ∀ l, l ≠ j → s l < s j) (hi : i ≠ j) :
    Tendsto (fun b : ℝ => scoreSoftmax b s i) atTop (𝓝 0) := by

  have hnum : Tendsto (fun b : ℝ => Real.exp (b * (s i - s j))) atTop (𝓝 0) :=
    tendsto_exp_mul_neg _ (by linarith [hmax i hi])
  have hden := tendsto_scoreSoftmax_denom s j hmax
  have hquot := hnum.div hden (by norm_num)
  have heq : ∀ b : ℝ, scoreSoftmax b s i
      = Real.exp (b * (s i - s j)) / ∑ l, Real.exp (b * (s l - s j)) := by
    intro b
    have hfac : ∑ l, Real.exp (b * s l)
        = Real.exp (b * s j) * ∑ l, Real.exp (b * (s l - s j)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [← Real.exp_add]
      ring_nf
    rw [scoreSoftmax, hfac, show Real.exp (b * s i)
        = Real.exp (b * s j) * Real.exp (b * (s i - s j)) by rw [← Real.exp_add]; ring_nf,
      mul_div_mul_left _ _ (Real.exp_ne_zero _)]
  simpa [heq, zero_div] using! hquot
