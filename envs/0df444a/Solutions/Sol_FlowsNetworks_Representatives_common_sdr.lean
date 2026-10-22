-- Prove2me | solution 1 for FlowsNetworks.Representatives.common_sdr
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T14:02:29.399761+00:00
-- url     : https://prove2.me/submissions/91d4accc-d6fa-4f7d-abb0-d62aa6a5b13b

import Mathlib
import Definitions.Def_FlowsNetworks_Representatives_SystemsOfRepresentatives
open FlowsNetworks.Representatives

theorem solution {m n : ℕ} (S T : Fin n → Finset (Fin m)) :
    (∃ (r : Fin n → Fin m) (σ : Equiv.Perm (Fin n)), IsCommonSDR S T r σ) ↔
      ∀ X Y : Finset (Fin n),
        X.card + Y.card ≤ n + (indexSet S X ∩ indexSet T Y).card := by
  constructor
  · rintro ⟨r, σ, hr, hrST⟩ X Y
    have h1 : X.image r ⊆ indexSet S X := by
      intro e he
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 he
      exact Finset.mem_biUnion.2 ⟨j, hj, (hrST j).1⟩
    have h2 : (Y.preimage σ σ.injective.injOn).image r ⊆ indexSet T Y := by
      intro e he
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 he
      rw [Finset.mem_preimage] at hj
      exact Finset.mem_biUnion.2 ⟨σ j, hj, (hrST j).2⟩
    have h3 : (Y.preimage σ σ.injective.injOn).card = Y.card := by
      have := Finset.card_preimage Y σ σ.injective.injOn
      rw [this]; congr 1
      ext k; simp only [Finset.mem_filter, and_iff_left_iff_imp]
      intro _; exact ⟨σ.symm k, by simp⟩
    have h4 := Finset.card_union_add_card_inter (X.image r)
      ((Y.preimage σ σ.injective.injOn).image r)
    rw [Finset.card_image_of_injective _ hr, Finset.card_image_of_injective _ hr, h3] at h4
    have h5 : (X.image r ∪ (Y.preimage σ σ.injective.injOn).image r).card ≤ n := by
      have hs : X.image r ∪ (Y.preimage σ σ.injective.injOn).image r ⊆ Finset.univ.image r :=
        Finset.union_subset (Finset.image_subset_image (Finset.subset_univ X))
          (Finset.image_subset_image (Finset.subset_univ _))
      exact (Finset.card_le_card hs).trans (Finset.card_image_le.trans (by simp))
    have h6 := Finset.card_le_card (Finset.inter_subset_inter h1 h2)
    omega
  · intro H
    let t : Fin n ⊕ Fin m → Finset (Fin m ⊕ Fin n) := fun z =>
      Sum.elim (fun j => (S j).map Function.Embedding.inl)
        (fun e => insert (Sum.inl e)
          ((Finset.univ.filter (fun k => e ∈ T k)).map Function.Embedding.inr)) z
    have hall : ∀ Z : Finset (Fin n ⊕ Fin m), Z.card ≤ (Z.biUnion t).card := by
      intro Z
      set X := Z.toLeft
      set F := Z.toRight
      set K := Finset.univ.filter (fun k => ∃ e ∈ F, e ∈ T k)
      have hZ : X.card + F.card = Z.card := Finset.card_toLeft_add_card_toRight
      have hsub : (indexSet S X ∪ F).disjSum K ⊆ Z.biUnion t := by
        intro w hw
        rcases w with e | k
        · rw [Finset.inl_mem_disjSum, Finset.mem_union] at hw
          rcases hw with he | he
          · obtain ⟨j, hj, hej⟩ := Finset.mem_biUnion.1 he
            exact Finset.mem_biUnion.2 ⟨Sum.inl j, Finset.mem_toLeft.1 hj, by simp [t, hej]⟩
          · exact Finset.mem_biUnion.2 ⟨Sum.inr e, Finset.mem_toRight.1 he, by simp [t]⟩
        · rw [Finset.inr_mem_disjSum] at hw
          simp only [K, Finset.mem_filter, Finset.mem_univ, true_and] at hw
          obtain ⟨e, he, hek⟩ := hw
          exact Finset.mem_biUnion.2 ⟨Sum.inr e, Finset.mem_toRight.1 he, by simp [t, hek]⟩
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_disjSum] at h1
      have h2 := H X Kᶜ
      rw [Finset.card_compl, Fintype.card_fin] at h2
      have h3 : indexSet S X ∩ indexSet T Kᶜ ⊆ indexSet S X \ F := by
        intro e he
        rw [Finset.mem_inter] at he
        rw [Finset.mem_sdiff]
        refine ⟨he.1, fun heF => ?_⟩
        obtain ⟨k, hk, hek⟩ := Finset.mem_biUnion.1 he.2
        rw [Finset.mem_compl] at hk
        exact hk (by simp only [K, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨e, heF, hek⟩)
      have h4 := Finset.card_le_card h3
      have h5 : (indexSet S X \ F).card + F.card = (indexSet S X ∪ F).card := by
        rw [← Finset.card_union_of_disjoint Finset.sdiff_disjoint, Finset.sdiff_union_self_eq_union]
      have h6 : K.card ≤ n := by simpa using Finset.card_le_univ K
      omega
    obtain ⟨f, hf, hft⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).1 hall
    have hbij : Function.Bijective f := (Fintype.bijective_iff_injective_and_card f).2
      ⟨hf, by simp [Fintype.card_sum]; omega⟩
    have hS : ∀ j, ∃ e, f (Sum.inl j) = Sum.inl e ∧ e ∈ S j := by
      intro j
      have := hft (Sum.inl j)
      simp only [t, Sum.elim_inl, Finset.mem_map, Function.Embedding.inl_apply] at this
      obtain ⟨e, he, h⟩ := this
      exact ⟨e, h.symm, he⟩
    choose r hr1 hr2 using hS
    have hT : ∀ j, ∃ k, f (Sum.inr (r j)) = Sum.inr k ∧ r j ∈ T k := by
      intro j
      have := hft (Sum.inr (r j))
      simp only [t, Sum.elim_inr, Finset.mem_insert, Finset.mem_map, Finset.mem_filter,
        Finset.mem_univ, true_and, Function.Embedding.inr_apply] at this
      rcases this with h | ⟨k, hk, h⟩
      · rw [← hr1 j] at h
        exact absurd (hf h) (by simp)
      · exact ⟨k, h.symm, hk⟩
    choose τ hτ1 hτ2 using hT
    have hrinj : Function.Injective r := by
      intro a b h
      have : f (Sum.inl a) = f (Sum.inl b) := by rw [hr1, hr1, h]
      exact Sum.inl_injective (hf this)
    have hτinj : Function.Injective τ := by
      intro a b h
      have : f (Sum.inr (r a)) = f (Sum.inr (r b)) := by rw [hτ1, hτ1, h]
      exact hrinj (Sum.inr_injective (hf this))
    have hτbij : Function.Bijective τ := (Fintype.bijective_iff_injective_and_card τ).2 ⟨hτinj, rfl⟩
    exact ⟨r, Equiv.ofBijective τ hτbij, hrinj, fun j => ⟨hr2 j, hτ2 j⟩⟩
