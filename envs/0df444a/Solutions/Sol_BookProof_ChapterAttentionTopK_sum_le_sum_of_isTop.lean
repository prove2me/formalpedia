-- Prove2me | solution 1 for BookProof.ChapterAttentionTopK.sum_le_sum_of_isTop
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T18:44:54.387981+00:00
-- url     : https://prove2.me/submissions/034d8b8a-71a5-40ca-97cc-9f698afb4c3f

-- Generated from ChapterAttentionTopK.lean — solution of BookProof.ChapterAttentionTopK.sum_le_sum_of_isTop
import Mathlib
import Definitions.Def_ChapterAttentionTopK
open BookProof.ChapterAttentionTopK



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution {p : Fin m → ℝ} (hp : ∀ x, 0 ≤ p x) {S T : Finset (Fin m)}
    (hS : IsTop p S) (hcard : T.card ≤ S.card) :
    ∑ x ∈ T, p x ≤ ∑ x ∈ S, p x := by

  have hsplitT : ∑ x ∈ T ∩ S, p x + ∑ x ∈ T \ S, p x = ∑ x ∈ T, p x :=
    Finset.sum_inter_add_sum_sdiff T S p
  have hsplitS : ∑ x ∈ S ∩ T, p x + ∑ x ∈ S \ T, p x = ∑ x ∈ S, p x :=
    Finset.sum_inter_add_sum_sdiff S T p
  have hinter : ∑ x ∈ T ∩ S, p x = ∑ x ∈ S ∩ T, p x := by rw [Finset.inter_comm]
  have hcardT := Finset.card_inter_add_card_sdiff T S
  have hcardS := Finset.card_inter_add_card_sdiff S T
  have hcardinter : (T ∩ S).card = (S ∩ T).card := by rw [Finset.inter_comm]
  have hdiffcard : (T \ S).card ≤ (S \ T).card := by omega
  have hdiff : ∑ x ∈ T \ S, p x ≤ ∑ x ∈ S \ T, p x := by
    rcases Finset.eq_empty_or_nonempty (S \ T) with hB | hB
    · have hBcard : (S \ T).card = 0 := by rw [hB]; simp
      have hA0 : (T \ S).card = 0 := by omega
      have hA : T \ S = ∅ := Finset.card_eq_zero.1 hA0
      simp [hA, hB]
    · obtain ⟨y₀, hy₀B, hy₀min⟩ := Finset.exists_min_image (S \ T) p hB
      have hy₀S : y₀ ∈ S := (Finset.mem_sdiff.1 hy₀B).1
      have hA : ∑ x ∈ T \ S, p x ≤ ((T \ S).card : ℝ) * p y₀ := by
        have := Finset.sum_le_card_nsmul (T \ S) p (p y₀) fun x hx => by
          exact hS y₀ hy₀S x (Finset.mem_sdiff.1 hx).2
        simpa [nsmul_eq_mul] using this
      have hBsum : ((S \ T).card : ℝ) * p y₀ ≤ ∑ x ∈ S \ T, p x := by
        have := Finset.card_nsmul_le_sum (S \ T) p (p y₀) fun x hx => hy₀min x hx
        simpa [nsmul_eq_mul] using this
      have hcards : ((T \ S).card : ℝ) ≤ ((S \ T).card : ℝ) := by exact_mod_cast hdiffcard
      have hy₀pos : 0 ≤ p y₀ := hp y₀
      calc ∑ x ∈ T \ S, p x ≤ ((T \ S).card : ℝ) * p y₀ := hA
        _ ≤ ((S \ T).card : ℝ) * p y₀ := mul_le_mul_of_nonneg_right hcards hy₀pos
        _ ≤ ∑ x ∈ S \ T, p x := hBsum
  rw [← hsplitT, ← hsplitS, hinter]
  linarith
