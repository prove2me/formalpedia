-- Prove2me | solution 1 for GalvinMultigraph.Local.hall_matching
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:05:14.771828+00:00
-- url     : https://prove2.me/submissions/a72bd815-cf64-4ea3-b292-a49251b8e19c

module
public import Definitions.Def_GalvinMultigraph_Local_Konig
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Set
public import Definitions.Def_GalvinMultigraph_Local_Ranks

set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false
open GalvinMultigraph GalvinMultigraph.Local
variable {U R E : Type*} [Fintype U] [Fintype R] [Fintype E]
  [DecidableEq U] [DecidableEq R] [DecidableEq E]
omit [Fintype U] [Fintype R] [Fintype E]
namespace GalvinMultigraph.Local
theorem _root_.solution (left : E → U) (right : E → R) (S : Finset E) (A : Finset U)
    (hAne : A.Nonempty)
    (hall : ∀ B ⊆ A,
      B.card ≤ (B.biUnion (fun u => (S.filter fun e => left e = u).image right)).card) :
    ∃ M : Finset E, M ⊆ S ∧ M.Nonempty ∧ IsMatchingOn left right M ∧
      (∀ u ∈ A, ∃ e ∈ M, left e = u) ∧ (∀ e ∈ M, left e ∈ A) ∧
      M.image right ⊆ A.biUnion (fun u => (S.filter fun e => left e = u).image right) ∧
      A.card ≤ (M.image right).card := by
  classical
  set nbr : U → Finset R := fun u => (S.filter fun e => left e = u).image right with hnbr
  have hall' : ∀ B : Finset ↥A, B.card ≤ (B.biUnion fun u => nbr u.val).card := by
    intro B
    have h1 : (B.image Subtype.val).card = B.card :=
      Finset.card_image_of_injective _ Subtype.val_injective
    have h2 : (B.image Subtype.val).biUnion nbr = B.biUnion fun u => nbr u.val := by
      ext r
      simp only [Finset.mem_biUnion, Finset.mem_image]
      constructor
      · rintro ⟨u, ⟨v, hv, rfl⟩, hr⟩
        exact ⟨v, hv, hr⟩
      · rintro ⟨v, hv, hr⟩
        exact ⟨v.val, ⟨v, hv, rfl⟩, hr⟩
    have hsub : B.image Subtype.val ⊆ A := by
      intro u hu
      obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hu
      exact v.2
    have := hall _ hsub
    rw [h1, h2] at this
    exact this
  obtain ⟨f, hfinj, hf⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective (fun u : ↥A => nbr u.val)).mp hall'
  have hex : ∀ u : ↥A, ∃ e, e ∈ S ∧ left e = u.val ∧ right e = f u := by
    intro u
    obtain ⟨e, he, hre⟩ := Finset.mem_image.mp (hf u)
    exact ⟨e, (Finset.mem_filter.mp he).1, (Finset.mem_filter.mp he).2, hre⟩
  choose g hgS hgl hgr using hex
  refine ⟨Finset.image g Finset.univ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp he
    exact hgS u
  · obtain ⟨u, hu⟩ := hAne
    exact ⟨g ⟨u, hu⟩, Finset.mem_image.mpr ⟨⟨u, hu⟩, Finset.mem_univ _, rfl⟩⟩
  · intro e he e' he' hne
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp he'
    have huv : u ≠ v := fun h => hne (by rw [h])
    refine ⟨?_, ?_⟩
    · rw [hgl u, hgl v]
      exact fun h => huv (Subtype.ext h)
    · rw [hgr u, hgr v]
      exact fun h => huv (hfinj h)
  · intro u hu
    exact ⟨g ⟨u, hu⟩, Finset.mem_image.mpr ⟨⟨u, hu⟩, Finset.mem_univ _, rfl⟩, hgl ⟨u, hu⟩⟩
  · intro e he
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp he
    rw [hgl u]
    exact u.2
  · intro r hr
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp he
    exact Finset.mem_biUnion.mpr ⟨u.val, u.2, by rw [hgr u]; exact hf u⟩
  · have himg : (Finset.image g Finset.univ).image right = Finset.univ.image f := by
      rw [Finset.image_image]
      exact Finset.image_congr (fun u _ => hgr u)
    rw [himg, Finset.card_image_of_injective _ hfinj, Finset.card_univ, Fintype.card_coe]
end GalvinMultigraph.Local
