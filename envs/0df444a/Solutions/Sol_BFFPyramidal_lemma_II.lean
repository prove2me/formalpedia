-- Prove2me | solution 1 for BFFPyramidal.lemma_II
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-13T18:51:43.464928+00:00
-- url     : https://prove2.me/submissions/005670c7-6916-4b9d-9317-4f0d755d3586

import Mathlib
open Pointwise

theorem solution {G : Type*} [Group G] [Finite G] (G₁ : Subgroup G)
    (hG₁ : G₁.index = Nat.minFac (Nat.card G)) (K : Subgroup G) (a : G) :
    (a • (K : Set G)) ⊆ (a • (G₁ : Set G)) ∨
      ∀ b : G, ((a • (K : Set G)) ∩ (b • (G₁ : Set G))).Nonempty := by
  classical
  -- `H` is `K ⊓ G₁`, viewed as a subgroup of `K`; its index in `K` is the number `r` of
  -- left cosets of `G₁` that `a • K` meets.
  set H : Subgroup K := G₁.subgroupOf K with hHdef
  -- the well-defined injection `K ⧸ H → G ⧸ G₁`, `k ↦ a * k`
  have hresp : ∀ k₁ k₂ : K, (QuotientGroup.leftRel H) k₁ k₂ →
      (QuotientGroup.mk (a * (k₁ : G)) : G ⧸ G₁) = QuotientGroup.mk (a * (k₂ : G)) := by
    intro k₁ k₂ h
    rw [QuotientGroup.leftRel_apply] at h
    have h' : ((k₁ : G)⁻¹ * (k₂ : G)) ∈ G₁ := by
      have h'' := Subgroup.mem_subgroupOf.mp h
      push_cast at h''
      exact h''
    rw [QuotientGroup.eq]
    have he : (a * (k₁ : G))⁻¹ * (a * (k₂ : G)) = (k₁ : G)⁻¹ * (k₂ : G) := by group
    rw [he]
    exact h'
  set f : K ⧸ H → G ⧸ G₁ := fun q =>
    Quotient.liftOn' q (fun k : K => (QuotientGroup.mk (a * (k : G)) : G ⧸ G₁)) hresp with hfdef
  have hf : ∀ k : K, f (QuotientGroup.mk k) = QuotientGroup.mk (a * (k : G)) := fun _ => rfl
  have hinj : Function.Injective f := by
    have key : ∀ k₁ k₂ : K, f (QuotientGroup.mk k₁) = f (QuotientGroup.mk k₂) →
        (QuotientGroup.mk k₁ : K ⧸ H) = QuotientGroup.mk k₂ := by
      intro k₁ k₂ h
      rw [hf, hf, QuotientGroup.eq] at h
      have he : (a * (k₁ : G))⁻¹ * (a * (k₂ : G)) = (k₁ : G)⁻¹ * (k₂ : G) := by group
      rw [he] at h
      rw [QuotientGroup.eq, hHdef, Subgroup.mem_subgroupOf]
      push_cast
      exact h
    intro q₁ q₂
    exact Quotient.inductionOn₂' q₁ q₂ key
  have hcardle : Nat.card (K ⧸ H) ≤ Nat.card (G ⧸ G₁) := Nat.card_le_card_of_injective f hinj
  have hp : Nat.card (G ⧸ G₁) = Nat.minFac (Nat.card G) := by
    rw [← Subgroup.index_eq_card]; exact hG₁
  have hidx : H.index = Nat.card (K ⧸ H) := Subgroup.index_eq_card H
  rcases eq_or_ne H.index 1 with h1 | h1
  · -- `r = 1` : `K ≤ G₁`, so `a • K ⊆ a • G₁`
    left
    have hKG₁ : K ≤ G₁ := Subgroup.subgroupOf_eq_top.mp (Subgroup.index_eq_one.mp h1)
    exact Set.smul_set_mono (SetLike.coe_subset_coe.mpr hKG₁)
  · -- `r > 1` : then `r = [G : G₁] = p`, so `a • K` meets every coset of `G₁`
    right
    have h0 : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hr2 : 2 ≤ H.index := by omega
    have hdvdK : H.index ∣ Nat.card K := H.index_dvd_card
    have hKG : Nat.card K ∣ Nat.card G := K.card_subgroup_dvd_card
    have hq : Nat.minFac H.index ∣ Nat.card G := (Nat.minFac_dvd _).trans (hdvdK.trans hKG)
    have h2q : 2 ≤ Nat.minFac H.index := (Nat.minFac_prime (by omega)).two_le
    have hple : Nat.minFac (Nat.card G) ≤ Nat.minFac H.index := Nat.minFac_le_of_dvd h2q hq
    have hqle : Nat.minFac H.index ≤ H.index := Nat.minFac_le (by omega)
    have heq : Nat.card (K ⧸ H) = Nat.card (G ⧸ G₁) := by omega
    have hsurj : Function.Surjective f :=
      ((Nat.bijective_iff_injective_and_card f).mpr ⟨hinj, heq⟩).2
    intro b
    obtain ⟨q, hq'⟩ := hsurj (QuotientGroup.mk b)
    have hout : (QuotientGroup.mk q.out : K ⧸ H) = q := QuotientGroup.out_eq' q
    have hmk : (QuotientGroup.mk (a * (q.out : G)) : G ⧸ G₁) = QuotientGroup.mk b := by
      rw [← hf, hout, hq']
    refine ⟨a * (q.out : G), ?_, ?_⟩
    · exact Set.smul_mem_smul_set q.out.2
    · rw [Set.mem_smul_set_iff_inv_smul_mem]
      have h3 : (a * (q.out : G))⁻¹ * b ∈ G₁ := QuotientGroup.eq.mp hmk
      have h4 : (b⁻¹ * (a * (q.out : G))) = ((a * (q.out : G))⁻¹ * b)⁻¹ := by group
      show b⁻¹ * (a * (q.out : G)) ∈ G₁
      rw [h4]
      exact G₁.inv_mem h3
