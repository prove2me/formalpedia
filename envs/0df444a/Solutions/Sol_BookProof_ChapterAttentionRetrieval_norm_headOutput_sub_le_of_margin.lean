-- Prove2me | solution 1 for BookProof.ChapterAttentionRetrieval.norm_headOutput_sub_le_of_margin
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T22:47:25.715198+00:00
-- url     : https://prove2.me/submissions/1ccecc81-b3ea-4bfa-80de-e6780120b8f5

-- Generated from ChapterAttentionRetrieval.lean — solution of BookProof.ChapterAttentionRetrieval.norm_headOutput_sub_le_of_margin
import Mathlib
import Definitions.Def_ChapterAttentionRetrieval
import Theorems.Thm_BookProof_ChapterAttentionRetrieval_card_erase_cast
import Theorems.Thm_BookProof_ChapterAttentionRetrieval_scoreSoftmax_le_exp_neg_margin
import Theorems.Thm_BookProof_ChapterAttentionOutput_headOutput_eq_sum
import Theorems.Thm_BookProof_ChapterSoftmaxOrder_scoreSoftmax_nonneg
import Theorems.Thm_BookProof_ChapterSoftmaxOrder_scoreSoftmax_sum_one
import Definitions.Def_ChapterAttentionOutput
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterAttentionOutput
open BookProof.ChapterAttentionRetrieval



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {m n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution {beta delta C : ℝ} (hb : 0 ≤ beta)
    (s : Fin m → ℝ) (v : Fin m → E) (j : Fin m)
    (hmargin : ∀ l, l ≠ j → s l + delta ≤ s j) (hv : ∀ l, ‖v l‖ ≤ C) :
    ‖headOutput beta s v - v j‖ ≤ 2 * C * (((m : ℝ) - 1) * Real.exp (-(beta * delta))) := by

  have hC : 0 ≤ C := le_trans (norm_nonneg _) (hv j)
  have hsum : ∑ l, scoreSoftmax beta s l = 1 := scoreSoftmax_sum_one beta s j
  have hdiff : headOutput beta s v - v j = ∑ l, scoreSoftmax beta s l • (v l - v j) := by
    rw [headOutput_eq_sum]
    rw [Finset.sum_congr rfl (fun l _ => smul_sub (scoreSoftmax beta s l) (v l) (v j)),
      Finset.sum_sub_distrib, ← Finset.sum_smul, hsum, one_smul]
  have hterm : ∀ l ∈ Finset.univ.erase j,
      ‖scoreSoftmax beta s l • (v l - v j)‖ ≤ 2 * C * Real.exp (-(beta * delta)) := by
    intro l hl
    have hpl : scoreSoftmax beta s l ≤ Real.exp (-(beta * delta)) :=
      scoreSoftmax_le_exp_neg_margin hb s (hmargin l (Finset.mem_erase.1 hl).1)
    have hvl : ‖v l - v j‖ ≤ 2 * C := by
      calc ‖v l - v j‖ ≤ ‖v l‖ + ‖v j‖ := norm_sub_le _ _
        _ ≤ C + C := add_le_add (hv l) (hv j)
        _ = 2 * C := by ring
    have hnn : (0 : ℝ) ≤ scoreSoftmax beta s l := scoreSoftmax_nonneg beta s l
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hnn]
    calc scoreSoftmax beta s l * ‖v l - v j‖
        ≤ Real.exp (-(beta * delta)) * (2 * C) := by
          apply mul_le_mul hpl hvl (norm_nonneg _) (Real.exp_pos _).le
      _ = 2 * C * Real.exp (-(beta * delta)) := by ring
  have hzero : scoreSoftmax beta s j • (v j - v j) = 0 := by simp
  have hsplit : ∑ l, scoreSoftmax beta s l • (v l - v j)
      = ∑ l ∈ Finset.univ.erase j, scoreSoftmax beta s l • (v l - v j) := by
    rw [← Finset.add_sum_erase Finset.univ (fun l => scoreSoftmax beta s l • (v l - v j))
      (Finset.mem_univ j), hzero, zero_add]
  rw [hdiff, hsplit]
  calc ‖∑ l ∈ Finset.univ.erase j, scoreSoftmax beta s l • (v l - v j)‖
      ≤ ∑ l ∈ Finset.univ.erase j, ‖scoreSoftmax beta s l • (v l - v j)‖ :=
        norm_sum_le _ _
    _ ≤ ((Finset.univ.erase j).card : ℝ) * (2 * C * Real.exp (-(beta * delta))) := by
        simpa [nsmul_eq_mul] using
          Finset.sum_le_card_nsmul (Finset.univ.erase j)
            (fun l => ‖scoreSoftmax beta s l • (v l - v j)‖)
            (2 * C * Real.exp (-(beta * delta))) hterm
    _ = 2 * C * (((m : ℝ) - 1) * Real.exp (-(beta * delta))) := by
        rw [card_erase_cast j]; ring
