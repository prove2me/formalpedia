-- Prove2me | solution 1 for BookProof.ChapterAttentionRetrieval.scoreSoftmax_ge_inv_of_margin
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T22:46:43.564568+00:00
-- url     : https://prove2.me/submissions/bce5e5fe-a28e-4a10-8010-d3c11a9d4ac5

-- Generated from ChapterAttentionRetrieval.lean — solution of BookProof.ChapterAttentionRetrieval.scoreSoftmax_ge_inv_of_margin
import Mathlib
import Definitions.Def_ChapterAttentionRetrieval
import Theorems.Thm_BookProof_ChapterAttentionRetrieval_card_erase_cast
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
theorem solution {beta delta : ℝ} (hb : 0 ≤ beta) (s : Fin m → ℝ)
    (j : Fin m) (hmargin : ∀ l, l ≠ j → s l + delta ≤ s j) :
    1 / (1 + ((m : ℝ) - 1) * Real.exp (-(beta * delta))) ≤ scoreSoftmax beta s j := by

  set c : ℝ := Real.exp (-(beta * delta)) with hc
  have hcpos : 0 < c := Real.exp_pos _
  have hcard : (0 : ℝ) ≤ (m : ℝ) - 1 := by
    have hm : 1 ≤ m := j.pos
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hEpos : (0 : ℝ) < Real.exp (beta * s j) := Real.exp_pos _
  -- the partition function is at most `exp (β s j) * (1 + (m-1) c)`
  have hZ : ∑ l, Real.exp (beta * s l) ≤ Real.exp (beta * s j) * (1 + ((m : ℝ) - 1) * c) := by
    have hsplit : ∑ l, Real.exp (beta * s l)
        = Real.exp (beta * s j) + ∑ l ∈ Finset.univ.erase j, Real.exp (beta * s l) :=
      (Finset.add_sum_erase Finset.univ (fun l => Real.exp (beta * s l))
        (Finset.mem_univ j)).symm
    have hterm : ∀ l ∈ Finset.univ.erase j,
        Real.exp (beta * s l) ≤ Real.exp (beta * s j) * c := by
      intro l hl
      have h := hmargin l (Finset.mem_erase.1 hl).1
      have hle : beta * s l ≤ beta * s j + -(beta * delta) := by
        have hd : delta ≤ s j - s l := by linarith
        have := mul_le_mul_of_nonneg_left hd hb
        nlinarith
      calc Real.exp (beta * s l) ≤ Real.exp (beta * s j + -(beta * delta)) :=
            Real.exp_le_exp.2 hle
        _ = Real.exp (beta * s j) * c := by rw [Real.exp_add, hc]
    have hbound := Finset.sum_le_card_nsmul (Finset.univ.erase j)
      (fun l => Real.exp (beta * s l)) (Real.exp (beta * s j) * c) hterm
    rw [nsmul_eq_mul, card_erase_cast j] at hbound
    rw [hsplit]
    nlinarith
  have hden : (0 : ℝ) < 1 + ((m : ℝ) - 1) * c := by positivity
  have hZpos : (0 : ℝ) < ∑ l, Real.exp (beta * s l) := scoreSoftmax_denom_pos beta s j
  rw [scoreSoftmax, div_le_div_iff₀ hden hZpos]
  linarith
