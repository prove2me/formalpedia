-- Prove2me | solution 1 for BookProof.ChapterAttentionLocality.farMass_le
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T16:43:14.578586+00:00
-- url     : https://prove2.me/submissions/d98eb1cf-6e90-406f-a315-eb5a52e655ca
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterAttentionLocality.lean — solution of BookProof.ChapterAttentionLocality.farMass_le
import Mathlib
import Definitions.Def_ChapterAttentionLocality
import Theorems.Thm_BookProof_ChapterAttentionLocality_scoreSoftmax_alibi_le
import Theorems.Thm_BookProof_ChapterAttentionLocality_mem_window
open BookProof.ChapterAttentionLocality



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution {beta gamma Delta R : ℝ} (hb : 0 ≤ beta) (hg : 0 ≤ gamma)
    (s : Fin m → ℝ) (d : Fin m → ℝ) {j₀ : Fin m} (hd0 : d j₀ = 0)
    (hDelta : ∀ l, s l ≤ s j₀ + Delta) :
    ∑ l ∈ (window d R)ᶜ, scoreSoftmax beta (alibiScore s gamma d) l
      ≤ (m : ℝ) * (Real.exp (beta * Delta) * Real.exp (-(beta * (gamma * R)))) := by

  have hterm : ∀ l ∈ (window d R)ᶜ,
      scoreSoftmax beta (alibiScore s gamma d) l
        ≤ Real.exp (beta * Delta) * Real.exp (-(beta * (gamma * R))) := by
    intro l hl
    have hfar : R ≤ d l := by
      have := Finset.mem_compl.1 hl
      rw [mem_window] at this
      linarith [not_lt.1 this]
    refine le_trans (scoreSoftmax_alibi_le hb s d hd0 hDelta l) ?_
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le
    have : gamma * R ≤ gamma * d l := mul_le_mul_of_nonneg_left hfar hg
    nlinarith [hb]
  calc ∑ l ∈ (window d R)ᶜ, scoreSoftmax beta (alibiScore s gamma d) l
      ≤ ∑ _l ∈ (window d R)ᶜ,
          Real.exp (beta * Delta) * Real.exp (-(beta * (gamma * R))) :=
        Finset.sum_le_sum hterm
    _ = ((window d R)ᶜ.card : ℝ)
          * (Real.exp (beta * Delta) * Real.exp (-(beta * (gamma * R)))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (m : ℝ) * (Real.exp (beta * Delta) * Real.exp (-(beta * (gamma * R)))) := by
        refine mul_le_mul_of_nonneg_right ?_
          (mul_pos (Real.exp_pos _) (Real.exp_pos _)).le
        have : (window d R)ᶜ.card ≤ m := by
          simpa using Finset.card_le_card (Finset.subset_univ ((window d R)ᶜ))
        exact_mod_cast this
