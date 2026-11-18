-- Prove2me | solution 1 for CompDesignBFM.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T04:28:06.848963+00:00
-- url     : https://prove2.me/submissions/66a5cc79-3648-413a-8192-244658cc664a

import Mathlib
import Definitions.Def_CompDesignBFM_IsSelfBounding
import Definitions.Def_CompDesignBFM_mcPay

open CompDesignBFM

theorem solution {n : ℕ} (F : Finset (Fin n) → ℝ) (B : ℝ) (hB : 0 < B) (hF0 : F ∅ = 0)
    (hF : IsSelfBounding F) (S : Finset (Fin n)) :
    (∀ i, 0 ≤ mcPay F B S i) ∧ ∑ i ∈ S, mcPay F B S i ≤ B := by
  obtain ⟨hnn, hmono, hsb⟩ := hF
  refine ⟨?_, ?_⟩
  · intro i
    unfold mcPay
    split_ifs with h
    · exact div_nonneg (mul_nonneg hB.le (sub_nonneg.2 (hmono _ _ (Finset.erase_subset i S)))) h.2.le
    · exact le_rfl
  · by_cases hpos : 0 < F S
    · have : ∑ i ∈ S, mcPay F B S i = ∑ i ∈ S, B * (F S - F (S.erase i)) / F S := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [mcPay, hi, hpos]
      rw [this, ← Finset.sum_div, ← Finset.mul_sum, div_le_iff₀ hpos]
      exact mul_le_mul_of_nonneg_left (hsb S) hB.le
    · have : ∑ i ∈ S, mcPay F B S i = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        simp [mcPay, hpos]
      rw [this]; exact hB.le
