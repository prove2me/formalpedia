-- Prove2me | solution 1 for CompDesign.Supplement.theorem_C_1
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T05:17:29.22596+00:00
-- url     : https://prove2.me/submissions/5d93082e-d87e-4def-bfe2-a25421d02c11

import Mathlib
import Definitions.Def_CompDesign_Supplement_IsPNEOf
import Definitions.Def_CompDesign_Supplement_IsCCEOf
import Definitions.Def_CompDesign_Supplement_targetedPay

set_option autoImplicit false
open CompDesign.Supplement

theorem solution {n : ℕ} (B : ℝ) (hB : 0 < B) (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    (T : Finset (Fin n)) (b : Fin n → ℝ) (hb : ∀ i ∈ T, 0 < b i)
    (hbud : ∑ i ∈ T, (c i + b i) ≤ B) (hout : ∀ i, i ∉ T → 0 < c i) :
    (∀ S : Finset (Fin n), IsPNEOf (targetedPay T c b) c S ↔ S = T) ∧
    ∀ μ : Finset (Fin n) → ℝ, IsCCEOf (targetedPay T c b) c μ → ∀ S, S ≠ T → μ S = 0 := by
  refine ⟨?_, ?_⟩
  · intro S
    constructor
    · rintro ⟨h1, h2⟩
      apply Finset.Subset.antisymm
      · intro i hi
        by_contra hiT
        have := h1 i hi
        have h0 : targetedPay T c b S i = 0 := by simp [targetedPay, hiT]
        have := hout i hiT
        linarith [h1 i hi]
      · intro i hiT
        by_contra hiS
        have := h2 i hiS
        have hv : targetedPay T c b (insert i S) i = c i + b i := by
          simp [targetedPay, hiT]
        have := hb i hiT
        linarith [h2 i hiS]
    · rintro rfl
      refine ⟨?_, ?_⟩
      · intro i hi
        have hv : targetedPay S c b S i = c i + b i := by simp [targetedPay, hi]
        have := hb i hi
        linarith
      · intro i hi
        have hv : targetedPay S c b (insert i S) i = 0 := by simp [targetedPay, hi]
        have := hc i
        linarith
  · intro μ hμ S hS
    obtain ⟨⟨hμ0, hμ1⟩, hμi⟩ := hμ
    have hz : ∀ i, (∀ S', i ∉ S' → μ S' = 0) ∨ (∀ S', i ∈ S' → μ S' = 0) → True := fun _ _ => trivial
    -- agents in the target are always in the support
    have hT : ∀ i ∈ T, ∀ S', i ∉ S' → μ S' = 0 := by
      intro i hiT S' hiS'
      obtain ⟨h1, _⟩ := hμi i
      unfold expect utilOf at h1
      have e1 : ∑ S'' : Finset (Fin n), μ S'' * (targetedPay T c b (insert i S'') i - c i) = b i := by
        have : ∀ S'' : Finset (Fin n), targetedPay T c b (insert i S'') i - c i = b i := by
          intro S''; simp [targetedPay, hiT]
        simp only [this]
        rw [← Finset.sum_mul, hμ1, one_mul]
      have e2 : ∑ S'' : Finset (Fin n), μ S'' * (if i ∈ S'' then targetedPay T c b S'' i - c i else 0) =
          b i * ∑ S'' ∈ Finset.univ.filter (fun S'' => i ∈ S''), μ S'' := by
        rw [Finset.mul_sum, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro S'' _
        by_cases h : i ∈ S''
        · simp [h, targetedPay, hiT]; ring
        · simp [h]
      rw [e1, e2] at h1
      have hbi := hb i hiT
      have hsum : ∑ S'' ∈ Finset.univ.filter (fun S'' => i ∈ S''), μ S'' ≥ 1 := by
        by_contra hlt
        push Not at hlt
        nlinarith
      have hsplit : ∑ S'' ∈ Finset.univ.filter (fun S'' => i ∈ S''), μ S'' +
          ∑ S'' ∈ Finset.univ.filter (fun S'' => i ∉ S''), μ S'' = 1 := by
        rw [Finset.sum_filter_add_sum_filter_not, hμ1]
      have hnot : ∑ S'' ∈ Finset.univ.filter (fun S'' => i ∉ S''), μ S'' ≤ 0 := by linarith
      have hnn : ∀ S'' ∈ Finset.univ.filter (fun S'' => i ∉ S''), 0 ≤ μ S'' :=
        fun S'' _ => hμ0 S''
      have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 (le_antisymm hnot (Finset.sum_nonneg hnn))
      exact this S' (by simp [hiS'])
    have hO : ∀ i, i ∉ T → ∀ S', i ∈ S' → μ S' = 0 := by
      intro i hiT S' hiS'
      obtain ⟨_, h2⟩ := hμi i
      unfold expect utilOf at h2
      have e : ∑ S'' : Finset (Fin n), μ S'' * (if i ∈ S'' then targetedPay T c b S'' i - c i else 0) =
          - c i * ∑ S'' ∈ Finset.univ.filter (fun S'' => i ∈ S''), μ S'' := by
        rw [Finset.mul_sum, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro S'' _
        by_cases h : i ∈ S''
        · simp [h, targetedPay, hiT]; ring
        · simp [h]
      rw [e] at h2
      have hci := hout i hiT
      have hnn : ∀ S'' ∈ Finset.univ.filter (fun S'' => i ∈ S''), 0 ≤ μ S'' :=
        fun S'' _ => hμ0 S''
      have hle : ∑ S'' ∈ Finset.univ.filter (fun S'' => i ∈ S''), μ S'' ≤ 0 := by
        by_contra hlt
        push Not at hlt
        nlinarith
      have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 (le_antisymm hle (Finset.sum_nonneg hnn))
      exact this S' (by simp [hiS'])
    by_cases hTS : T ⊆ S
    · have : ∃ i, i ∈ S ∧ i ∉ T := by
        by_contra hcon
        push Not at hcon
        exact hS (Finset.Subset.antisymm (fun i hi => hcon i hi) hTS)
      obtain ⟨i, hiS, hiT⟩ := this
      exact hO i hiT S hiS
    · rw [Finset.not_subset] at hTS
      obtain ⟨i, hiT, hiS⟩ := hTS
      exact hT i hiT S hiS
