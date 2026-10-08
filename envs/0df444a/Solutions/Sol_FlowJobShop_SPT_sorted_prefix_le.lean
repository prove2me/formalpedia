-- Prove2me | solution 1 for FlowJobShop.SPT.sorted_prefix_le
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T12:58:35.966371+00:00
-- url     : https://prove2.me/submissions/6a14d330-78b0-41e6-ad18-937942a72220

import Mathlib



namespace FlowJobShop.SPT

theorem spl_core {n : ℕ} (L : Fin n → ℝ) (σ : Fin n ≃ Fin n)
    (hσ : Monotone fun k => L (σ k)) (ρ : Fin n ≃ Fin n) (k : Fin n) :
    ∑ j ∈ Finset.Iic k, L (σ j) ≤ ∑ j ∈ Finset.Iic k, L (ρ j) := by
  classical
  set a : Fin n → ℝ := fun i => L (σ i) with ha
  have hL : ∀ x, L x = a (σ.symm x) := by intro x; simp [ha]
  have h2 : ∑ j ∈ Finset.Iic k, L (ρ j) = ∑ j ∈ (Finset.Iic k).map (ρ.trans σ.symm).toEmbedding, a j := by
    rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro j _
    simp [hL]
  rw [h2]
  set I := Finset.Iic k with hI
  set T := I.map (ρ.trans σ.symm).toEmbedding with hT
  have hc : T.card = I.card := by simp [hT]
  have hc2 : (T \ I).card = (I \ T).card := Finset.card_sdiff_comm hc
  have e1 : ∑ j ∈ T, a j = ∑ j ∈ T \ I, a j + ∑ j ∈ T ∩ I, a j := by
    rw [← Finset.sum_union (Finset.disjoint_sdiff_inter T I), Finset.sdiff_union_inter]
  have e2 : ∑ j ∈ I, a j = ∑ j ∈ I \ T, a j + ∑ j ∈ T ∩ I, a j := by
    rw [Finset.inter_comm, ← Finset.sum_union (Finset.disjoint_sdiff_inter I T), Finset.sdiff_union_inter]
  have b1 : ∑ j ∈ I \ T, a j ≤ (I \ T).card • a k := by
    apply Finset.sum_le_card_nsmul
    intro x hx
    have : x ≤ k := by simpa [hI] using (Finset.mem_sdiff.1 hx).1
    exact hσ this
  have b2 : (T \ I).card • a k ≤ ∑ j ∈ T \ I, a j := by
    apply Finset.card_nsmul_le_sum
    intro x hx
    have : ¬ x ≤ k := by simpa [hI] using (Finset.mem_sdiff.1 hx).2
    exact hσ (le_of_lt (not_le.1 this))
  rw [hc2] at b2
  linarith

end FlowJobShop.SPT

open FlowJobShop.SPT


theorem solution {n : ℕ} (L : Fin n → ℝ) (σ : Fin n ≃ Fin n)
    (hσ : Monotone fun k => L (σ k)) (ρ : Fin n ≃ Fin n) (k : Fin n) :
    ∑ j ∈ Finset.Iic k, L (σ j) ≤ ∑ j ∈ Finset.Iic k, L (ρ j) := by
  exact spl_core L σ hσ ρ k
