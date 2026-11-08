-- Prove2me | solution 1 for ConitzerFPPE.Core.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:14:02.926023+00:00
-- url     : https://prove2.me/submissions/e9396b35-6dc2-4f35-ad41-594721c33341

import Definitions.Def_ConitzerFPPE_Core_IsBFPM
import Definitions.Def_ConitzerFPPE_Core_revenue

open ConitzerFPPE.Core in
theorem solution {N M : Type*} [Fintype N] [Fintype M]
    (P : MultPacing.Existence.PacingGame N M) (α₁ α₂ : N → ℝ) (x₁ x₂ : N → M → ℝ)
    (h₁ : IsBFPM P α₁ x₁) (h₂ : IsBFPM P α₂ x₂)
    (hdom : ∀ i, α₂ i ≤ α₁ i) :
    revenue P α₂ x₂ ≤ revenue P α₁ x₁ := by
  have hprice_nonneg : ∀ (α : N → ℝ) (j : M), 0 ≤ price P α j := by
    intro α j
    unfold price
    exact Finset.le_sup'_of_le _ (Finset.mem_univ none) (le_refl _)
  have hmono : ∀ j, price P α₂ j ≤ price P α₁ j := by
    intro j
    unfold price
    apply Finset.sup'_le
    intro k _
    cases k with
    | none => exact Finset.le_sup'_of_le _ (Finset.mem_univ none) (le_refl _)
    | some i =>
      exact Finset.le_sup'_of_le _ (Finset.mem_univ (some i))
        (mul_le_mul_of_nonneg_right (hdom i) (P.v_nonneg i j))
  have hrev : ∀ (α : N → ℝ) (x : N → M → ℝ), IsBFPM P α x →
      revenue P α x = ∑ j, price P α j := by
    intro α x h
    unfold revenue spend
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Finset.sum_mul]
    rcases (hprice_nonneg α j).lt_or_eq with hp | hp
    · rw [h.positive_price_clearance j hp, one_mul]
    · rw [← hp, mul_zero]
  rw [hrev α₂ x₂ h₂, hrev α₁ x₁ h₁]
  exact Finset.sum_le_sum (fun j _ => hmono j)
