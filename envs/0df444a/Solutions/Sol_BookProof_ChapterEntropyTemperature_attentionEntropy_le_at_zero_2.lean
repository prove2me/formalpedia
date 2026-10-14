-- Prove2me | solution 2 for BookProof.ChapterEntropyTemperature.attentionEntropy_le_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T12:20:54.650532+00:00
-- url     : https://prove2.me/submissions/fa3068e0-1450-4ede-b576-59bf5f8a4caf

-- Generated from ChapterEntropyTemperature.lean — theorem BookProof.ChapterEntropyTemperature.attentionEntropy_le_at_zero
import Definitions.Def_ChapterAttentionEntropy
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib
import Definitions.Def_ChapterEntropyTemperature
open BookProof.ChapterEntropyTemperature


open scoped BigOperators

noncomputable section


open BookProof.ChapterAttentionEntropy BookProof.ChapterSoftmaxSharpness

variable {m : ℕ}
open BookProof.ChapterEntropyTemperature

theorem solution(s : Fin m → ℝ) (i : Fin m) {beta : ℝ}
    (hbeta : 0 ≤ beta) : attentionEntropy beta s ≤ attentionEntropy 0 s := by
  have hm : (0:ℝ) < m := by exact_mod_cast i.pos
  have hpos : ∀ b : ℝ, ∀ j, 0 < scoreSoftmax b s j := by
    intro b j
    unfold scoreSoftmax
    exact div_pos (Real.exp_pos _) (Finset.sum_pos (fun l _ => Real.exp_pos _) ⟨i, Finset.mem_univ _⟩)
  have hsum : ∑ j, scoreSoftmax beta s j = 1 := by
    unfold scoreSoftmax
    rw [← Finset.sum_div]
    exact div_self (Finset.sum_pos (fun l _ => Real.exp_pos _) ⟨i, Finset.mem_univ _⟩).ne'
  have h0 : attentionEntropy 0 s = Real.log m := by
    unfold attentionEntropy shannonEntropy scoreSoftmax
    simp [Real.log_inv]
    field_simp
  rw [h0]
  have key : ∀ j, -(scoreSoftmax beta s j * Real.log (scoreSoftmax beta s j)) - scoreSoftmax beta s j * Real.log m ≤ 1 / m - scoreSoftmax beta s j := by
    intro j
    have hp := hpos beta j
    have hl := Real.log_le_sub_one_of_pos (div_pos one_pos (mul_pos hm hp))
    rw [one_div, Real.log_inv, Real.log_mul hm.ne' hp.ne'] at hl
    have mm := mul_le_mul_of_nonneg_left hl hp.le
    have e : scoreSoftmax beta s j * ((m * scoreSoftmax beta s j)⁻¹ - 1) = 1 / m - scoreSoftmax beta s j := by
      field_simp
    rw [e] at mm
    nlinarith [mm]
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => key j)
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, Finset.sum_neg_distrib] at hs
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  unfold attentionEntropy shannonEntropy
  have : (m:ℝ) * (1 / m) = 1 := by field_simp
  linarith
