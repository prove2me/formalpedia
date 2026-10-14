-- Prove2me | solution 1 for BookProof.ChapterSoftmaxDivergence.klDiv_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T12:00:59.615986+00:00
-- url     : https://prove2.me/submissions/91b871ef-2762-4dde-8bcc-faad27fcda4d

-- Generated from ChapterSoftmaxDivergence.lean — theorem BookProof.ChapterSoftmaxDivergence.klDiv_nonneg
import Definitions.Def_ChapterAttentionEntropy
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib
import Definitions.Def_ChapterSoftmaxDivergence
open BookProof.ChapterSoftmaxDivergence


open scoped BigOperators

noncomputable section


open BookProof.ChapterAttentionEntropy BookProof.ChapterSoftmaxSharpness

variable {m : ℕ}
open BookProof.ChapterSoftmaxDivergence

theorem solution{p q : Fin m → ℝ} (hp0 : ∀ j, 0 ≤ p j) (hpsum : ∑ j, p j = 1)
    (hq0 : ∀ j, 0 < q j) (hqsum : ∑ j, q j ≤ 1) : 0 ≤ klDiv p q := by
  have key : ∀ j, p j - q j ≤ p j * Real.log (p j / q j) := by
    intro j
    rcases (hp0 j).eq_or_lt with h | h
    · rw [← h]
      simp <;> linarith [hq0 j]
    · have hl := Real.log_le_sub_one_of_pos (div_pos (hq0 j) h)
      rw [Real.log_div (hq0 j).ne' h.ne'] at hl
      rw [Real.log_div h.ne' (hq0 j).ne']
      have m := mul_le_mul_of_nonneg_left hl h.le
      have e : p j * (q j / p j - 1) = q j - p j := by field_simp
      rw [e] at m
      nlinarith [m]
  unfold klDiv
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => key j)
  rw [Finset.sum_sub_distrib, hpsum] at hs
  linarith
