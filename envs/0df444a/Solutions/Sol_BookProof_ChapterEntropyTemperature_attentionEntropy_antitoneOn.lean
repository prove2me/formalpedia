-- Prove2me | solution 1 for BookProof.ChapterEntropyTemperature.attentionEntropy_antitoneOn
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T10:50:49.054231+00:00
-- url     : https://prove2.me/submissions/9611bb43-0b56-4a2b-90e3-813e281eef15

import Definitions.Def_ChapterAttentionEntropy
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib
import Theorems.Thm_BookProof_ChapterEntropyTemperature_hasDerivAt_attentionEntropy
import Theorems.Thm_BookProof_ChapterEntropyTemperature_heatCapacity_nonneg
import Definitions.Def_ChapterEntropyTemperature
-- Generated from ChapterEntropyTemperature.lean — theorem BookProof.ChapterEntropyTemperature.attentionEntropy_antitoneOn
open BookProof.ChapterEntropyTemperature


open scoped BigOperators

noncomputable section


open BookProof.ChapterAttentionEntropy BookProof.ChapterSoftmaxSharpness

variable {m : ℕ}
theorem solution (s : Fin m → ℝ) (i : Fin m) :
    AntitoneOn (fun b : ℝ => attentionEntropy b s) (Set.Ici (0 : ℝ)) := by
  have hd := fun b : ℝ => BookProof.ChapterEntropyTemperature.hasDerivAt_attentionEntropy b s i
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
  · exact fun b _ => (hd b).continuousAt.continuousWithinAt
  · exact fun b _ => (hd b).differentiableAt.differentiableWithinAt
  · intro b hb
    rw [interior_Ici, Set.mem_Ioi] at hb
    rw [(hd b).deriv]
    have hc := BookProof.ChapterEntropyTemperature.heatCapacity_nonneg b s
    unfold heatCapacity at hc
    have hv : 0 ≤ BookProof.ChapterSoftmaxFluctuation.varScore b s := by
      by_contra h
      push Not at h
      have : b ^ 2 * BookProof.ChapterSoftmaxFluctuation.varScore b s < 0 := mul_neg_of_pos_of_neg (by positivity) h
      linarith
    have := mul_nonneg hb.le hv
    linarith
