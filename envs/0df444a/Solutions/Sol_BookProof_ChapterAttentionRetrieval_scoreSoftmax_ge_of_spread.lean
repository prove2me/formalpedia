-- Prove2me | solution 1 for BookProof.ChapterAttentionRetrieval.scoreSoftmax_ge_of_spread
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T22:47:26.829922+00:00
-- url     : https://prove2.me/submissions/d7deae07-2a7c-4657-b59a-0fb4e9d0f82d

-- Generated from ChapterAttentionRetrieval.lean — solution of BookProof.ChapterAttentionRetrieval.scoreSoftmax_ge_of_spread
import Mathlib
import Definitions.Def_ChapterAttentionRetrieval
import Theorems.Thm_BookProof_ChapterSoftmaxOrder_scoreSoftmax_denom_pos
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterAttentionRetrieval



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {m n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution {beta D : ℝ} (hb : 0 ≤ beta) (s : Fin m → ℝ)
    (j : Fin m) (hD : ∀ l, s l ≤ s j + D) :
    Real.exp (-(beta * D)) / (m : ℝ) ≤ scoreSoftmax beta s j := by

  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast j.pos
  have hEpos : (0 : ℝ) < Real.exp (beta * s j) := Real.exp_pos _
  have hZpos : (0 : ℝ) < ∑ l, Real.exp (beta * s l) := scoreSoftmax_denom_pos beta s j
  have hZ : ∑ l, Real.exp (beta * s l)
      ≤ (m : ℝ) * (Real.exp (beta * s j) * Real.exp (beta * D)) := by
    have hterm : ∀ l ∈ (Finset.univ : Finset (Fin m)),
        Real.exp (beta * s l) ≤ Real.exp (beta * s j) * Real.exp (beta * D) := by
      intro l _
      have hle : beta * s l ≤ beta * s j + beta * D := by
        have := mul_le_mul_of_nonneg_left (hD l) hb
        nlinarith
      calc Real.exp (beta * s l) ≤ Real.exp (beta * s j + beta * D) := Real.exp_le_exp.2 hle
        _ = Real.exp (beta * s j) * Real.exp (beta * D) := Real.exp_add _ _
    have := Finset.sum_le_card_nsmul (Finset.univ : Finset (Fin m))
      (fun l => Real.exp (beta * s l)) (Real.exp (beta * s j) * Real.exp (beta * D)) hterm
    simpa [nsmul_eq_mul] using this
  have hexp : Real.exp (-(beta * D)) * Real.exp (beta * D) = 1 := by
    rw [← Real.exp_add]; simp
  have hmul := mul_le_mul_of_nonneg_left hZ (Real.exp_pos (-(beta * D))).le
  have hrewrite : Real.exp (-(beta * D)) *
      ((m : ℝ) * (Real.exp (beta * s j) * Real.exp (beta * D)))
      = Real.exp (beta * s j) * (m : ℝ) := by
    calc Real.exp (-(beta * D)) *
          ((m : ℝ) * (Real.exp (beta * s j) * Real.exp (beta * D)))
        = (m : ℝ) * Real.exp (beta * s j) *
            (Real.exp (-(beta * D)) * Real.exp (beta * D)) := by ring
      _ = Real.exp (beta * s j) * (m : ℝ) := by rw [hexp]; ring
  rw [scoreSoftmax, div_le_div_iff₀ hmpos hZpos]
  linarith
