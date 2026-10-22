-- Prove2me | solution 1 for FlowsNetworks.Representatives.sdr_marginal_hall
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T13:53:57.646235+00:00
-- url     : https://prove2.me/submissions/77ea2d0d-9bdf-48c9-bb02-2c9e40ac0348

import Mathlib
import Definitions.Def_FlowsNetworks_Representatives_SystemsOfRepresentatives
open FlowsNetworks.Representatives

theorem g70fn2_marg {ι E : Type} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (S : ι → Finset E) (M : Finset E) :
    (∃ r : ι → E, Function.Injective r ∧ (∀ j, r j ∈ S j) ∧ M ⊆ Finset.univ.image r) ↔
      ∀ X : Finset ι, X.card ≤ (X.biUnion S).card ∧
        X.card + M.card ≤ Fintype.card ι + (M ∩ X.biUnion S).card := by
  constructor
  · rintro ⟨r, hr, hrS, hM⟩ X
    constructor
    · rw [← Finset.card_image_of_injective X hr]
      apply Finset.card_le_card
      intro e he
      simp only [Finset.mem_image] at he
      obtain ⟨j, hj, rfl⟩ := he
      exact Finset.mem_biUnion.2 ⟨j, hj, hrS j⟩
    · have h1 : M \ X.biUnion S ⊆ Xᶜ.image r := by
        intro e he
        rw [Finset.mem_sdiff] at he
        obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 (hM he.1)
        refine Finset.mem_image.2 ⟨j, ?_, rfl⟩
        rw [Finset.mem_compl]
        intro hj
        exact he.2 (Finset.mem_biUnion.2 ⟨j, hj, hrS j⟩)
      have h2 := Finset.card_le_card h1
      have h3 := Finset.card_image_le (s := Xᶜ) (f := r)
      rw [Finset.card_compl] at h3
      have h4 : (M \ X.biUnion S).card + (M ∩ X.biUnion S).card = M.card :=
        Finset.card_sdiff_add_card_inter M _
      have h5 := Finset.card_le_univ X
      omega
  · intro H
    have hle : Fintype.card ι ≤ Fintype.card E := by
      have := (H Finset.univ).1
      rw [Finset.card_univ] at this
      exact this.trans (Finset.card_le_univ _)
    let D := Fin (Fintype.card E - Fintype.card ι)
    let T : ι ⊕ D → Finset E := fun z => Sum.elim S (fun _ => Mᶜ) z
    have hall : ∀ Z : Finset (ι ⊕ D), Z.card ≤ (Z.biUnion T).card := by
      intro Z
      have hZ := Finset.card_toLeft_add_card_toRight (u := Z)
      have hsub1 : Z.toLeft.biUnion S ⊆ Z.biUnion T := by
        intro e he
        obtain ⟨j, hj, hej⟩ := Finset.mem_biUnion.1 he
        exact Finset.mem_biUnion.2 ⟨Sum.inl j, Finset.mem_toLeft.1 hj, hej⟩
      by_cases hY : Z.toRight = ∅
      · rw [hY, Finset.card_empty] at hZ
        have := (H Z.toLeft).1
        have := Finset.card_le_card hsub1
        omega
      · obtain ⟨d, hd⟩ := Finset.nonempty_iff_ne_empty.2 hY
        have hsub2 : (M ∩ Z.toLeft.biUnion S) ∪ Mᶜ ⊆ Z.biUnion T := by
          intro e he
          rcases Finset.mem_union.1 he with he | he
          · exact hsub1 (Finset.mem_inter.1 he).2
          · exact Finset.mem_biUnion.2 ⟨Sum.inr d, Finset.mem_toRight.1 hd, he⟩
        have hdisj : Disjoint (M ∩ Z.toLeft.biUnion S) Mᶜ :=
          Finset.disjoint_left.2 fun e he he' =>
            (Finset.mem_compl.1 he') (Finset.mem_inter.1 he).1
        have h1 := Finset.card_le_card hsub2
        rw [Finset.card_union_of_disjoint hdisj, Finset.card_compl] at h1
        have h2 := (H Z.toLeft).2
        have h3 : Z.toRight.card ≤ Fintype.card E - Fintype.card ι := by
          have := Finset.card_le_univ Z.toRight
          simpa [D] using this
        have h4 := Finset.card_le_card (Finset.subset_univ M)
        rw [Finset.card_univ] at h4
        omega
    obtain ⟨f, hf, hfT⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective T).1 hall
    have hcard : Fintype.card (ι ⊕ D) = Fintype.card E := by
      simp [D, Fintype.card_sum]; omega
    have hbij : Function.Bijective f := (Fintype.bijective_iff_injective_and_card f).2 ⟨hf, hcard⟩
    refine ⟨fun j => f (Sum.inl j), fun a b h => Sum.inl_injective (hf h),
      fun j => hfT (Sum.inl j), ?_⟩
    intro e he
    obtain ⟨z, rfl⟩ := hbij.2 e
    rcases z with j | d
    · exact Finset.mem_image.2 ⟨j, Finset.mem_univ _, rfl⟩
    · exact absurd he (Finset.mem_compl.1 (hfT (Sum.inr d)))

theorem solution {m n : ℕ} (S : Fin n → Finset (Fin m)) (M : Finset (Fin m)) :
    (∃ r : Fin n → Fin m, IsSDR S r ∧ M ⊆ Finset.univ.image r) ↔
      ((∀ X : Finset (Fin n), X.card ≤ (indexSet S X).card) ∧
        ∀ M' ⊆ M, M'.card ≤ (Finset.univ.filter (fun j => (S j ∩ M').Nonempty)).card) := by
  have key := g70fn2_marg S M
  simp only [Fintype.card_fin] at key
  constructor
  · rintro ⟨r, ⟨hr, hrS⟩, hM⟩
    refine ⟨fun X => (key.1 ⟨r, hr, hrS, hM⟩ X).1, ?_⟩
    intro M' hM'
    have h1 : M' ⊆ (Finset.univ.filter (fun j => (S j ∩ M').Nonempty)).image r := by
      intro e he
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 (hM (hM' he))
      refine Finset.mem_image.2 ⟨j, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨r j, Finset.mem_inter.2 ⟨hrS j, he⟩⟩
    exact (Finset.card_le_card h1).trans Finset.card_image_le
  · rintro ⟨hH, hM'⟩
    obtain ⟨r, hr, hrS, hM⟩ := key.2 (fun X => by
      refine ⟨hH X, ?_⟩
      have h1 := hM' (M \ X.biUnion S) Finset.sdiff_subset
      have h2 : Finset.univ.filter (fun j => (S j ∩ (M \ X.biUnion S)).Nonempty) ⊆ Xᶜ := by
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        obtain ⟨e, he⟩ := hj
        rw [Finset.mem_inter, Finset.mem_sdiff] at he
        rw [Finset.mem_compl]
        intro hjX
        exact he.2.2 (Finset.mem_biUnion.2 ⟨j, hjX, he.1⟩)
      have h3 := Finset.card_le_card h2
      rw [Finset.card_compl, Fintype.card_fin] at h3
      have h4 : (M \ X.biUnion S).card + (M ∩ X.biUnion S).card = M.card :=
        Finset.card_sdiff_add_card_inter M _
      have h5 := Finset.card_le_univ X
      rw [Fintype.card_fin] at h5
      omega)
    exact ⟨r, ⟨hr, hrS⟩, hM⟩
