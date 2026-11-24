-- Prove2me | solution 1 for FiniteGroupTesting.LinearQuery.Supplement.lemma_4_5
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-23T23:31:06.703719+00:00
-- url     : https://prove2.me/submissions/64d4f84f-3f7f-4b87-bf72-d59826ef09c7

import Definitions.Def_FiniteGroupTesting_LinearQuery_Supplement_PartialMaps

set_option autoImplicit false

open FiniteGroupTesting.LinearQuery FiniteGroupTesting.LinearQuery.Supplement

theorem solution {G H : Type} [Fintype G] [Fintype H] [Nonempty G]
    [Nonempty H] (hcard : Fintype.card G = Fintype.card H) (ψ : PartialMap G H) :
    IsLeast (Set.range (bijectionError ψ)) (defect ψ) := by
  classical
  have hnpos : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  -- the error of a bijection, through the size of its agreement set
  have herr : ∀ π : G ≃ H, bijectionError ψ π =
      1 - ((Finset.univ.filter fun x => ψ x = some (π x)).card : ℝ) / Fintype.card G := by
    intro π
    have h1 := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset G)) (fun x => ψ x = some (π x))
    rw [Finset.card_univ] at h1
    have h2 : bijectionError ψ π =
        ((Finset.univ.filter fun x => ¬ ψ x = some (π x)).card : ℝ) / Fintype.card G := by
      unfold bijectionError uniformProbability
      convert rfl
    rw [h2, eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq hnpos.ne']
    have h3 : (Finset.univ.filter fun x => ¬ ψ x = some (π x)).card +
        (Finset.univ.filter fun x => ψ x = some (π x)).card = Fintype.card G := by omega
    exact_mod_cast h3
  -- every agreement set injects into the image
  have hle : ∀ π : G ≃ H, (Finset.univ.filter fun x => ψ x = some (π x)).card ≤
      (imageSet ψ).card := by
    intro π
    apply Finset.card_le_card_of_injOn π
    · intro x hx
      simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
        Set.mem_setOf_eq, Finset.mem_coe] at hx
      simp only [imageSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.coe_filter,
        Set.mem_setOf_eq, Finset.mem_coe]
      exact ⟨x, hx⟩
    · exact π.injective.injOn
  -- a bijection agreeing with ψ on one chosen preimage of every image point
  have hpre : ∀ h : imageSet ψ, ∃ x, ψ x = some (h : H) := by
    intro h
    have := h.2
    simp only [imageSet, Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact this
  choose pre hpre using hpre
  have pre_inj : Function.Injective pre := by
    intro a b hab
    apply Subtype.ext
    have := hpre a
    rw [hab, hpre b] at this
    exact (Option.some_injective _ this).symm
  let e0 : G ≃ H := Fintype.equivOfCardEq hcard
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair (fun h : imageSet ψ => e0 (pre h))
    (fun h : imageSet ψ => (h : H)) (e0.injective.comp pre_inj) Subtype.val_injective
  let π : G ≃ H := e0.trans σ
  have hπ : ∀ h : imageSet ψ, π (pre h) = h := fun h => hσ h
  have hge : (imageSet ψ).card ≤ (Finset.univ.filter fun x => ψ x = some (π x)).card := by
    have hsub : (Finset.univ.image pre) ⊆ Finset.univ.filter fun x => ψ x = some (π x) := by
      intro x hx
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
      obtain ⟨h, rfl⟩ := hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hpre h, hπ h]
    calc (imageSet ψ).card = Fintype.card (imageSet ψ) := (Fintype.card_coe _).symm
      _ = (Finset.univ.image pre).card := by
        rw [Finset.card_image_of_injective _ pre_inj, Finset.card_univ]
      _ ≤ _ := Finset.card_le_card hsub
  refine ⟨⟨π, ?_⟩, ?_⟩
  · rw [herr π]
    unfold defect
    rw [le_antisymm (hle π) hge]
  · rintro r ⟨π', rfl⟩
    rw [herr π']
    unfold defect
    have h1 : ((Finset.univ.filter fun x => ψ x = some (π' x)).card : ℝ) ≤ (imageSet ψ).card := by
      exact_mod_cast hle π'
    have h2 : ((Finset.univ.filter fun x => ψ x = some (π' x)).card : ℝ) / Fintype.card G ≤
        ((imageSet ψ).card : ℝ) / Fintype.card G := by gcongr
    linarith
