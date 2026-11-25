-- Prove2me | solution 1 for GalvinMultigraph.Local.matching_dichotomy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:08:43.702057+00:00
-- url     : https://prove2.me/submissions/79041fa1-3ac9-4a79-89f3-869d4aea4107

module
public import Definitions.Def_GalvinMultigraph_Local_Konig
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Set
public import Definitions.Def_GalvinMultigraph_Local_Ranks
public import Theorems.Thm_GalvinMultigraph_Local_hall_matching

set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false
open GalvinMultigraph GalvinMultigraph.Local
variable {U R E : Type*} [Fintype U] [Fintype R] [Fintype E]
  [DecidableEq U] [DecidableEq R] [DecidableEq E]
omit [Fintype R] [Fintype E]
namespace GalvinMultigraph.Local
theorem _root_.solution (left : E → U) (right : E → R) (S : Finset E) (hS : S.Nonempty) :
    ∃ M : Finset E, M ⊆ S ∧ M.Nonempty ∧ IsMatchingOn left right M ∧
      ((∀ e ∈ S, ∃ f ∈ M, left f = left e) ∨
       (∀ e ∈ S, (∃ f ∈ M, left f = left e) → ∃ f ∈ M, right f = right e)) := by
  classical
  set nbr : U → Finset R := fun u => (S.filter fun e => left e = u).image right with hnbr
  by_cases hall : ∀ B ⊆ S.image left, B.card ≤ (B.biUnion nbr).card
  · -- Hall's condition holds: a matching covering all left vertices.
    obtain ⟨e0, he0⟩ := hS
    obtain ⟨M, hMS, hMne, hM, hcov, _, _, _⟩ :=
      hall_matching left right S (S.image left) ⟨left e0, Finset.mem_image_of_mem _ he0⟩ hall
    exact ⟨M, hMS, hMne, hM, Or.inl fun e he => hcov (left e) (Finset.mem_image_of_mem _ he)⟩
  · -- Hall's condition fails: a minimal violating set minus one vertex is tight.
    push Not at hall
    obtain ⟨B0, hB0sub, hB0⟩ := hall
    set bad : Finset (Finset U) :=
      (Finset.univ : Finset (Finset U)).filter
        (fun B => B ⊆ S.image left ∧ (B.biUnion nbr).card < B.card) with hbad
    have hbadne : bad.Nonempty := ⟨B0, by simp [hbad, hB0sub, hB0]⟩
    obtain ⟨A, hAbad, hAmin⟩ := Finset.exists_min_image bad Finset.card hbadne
    obtain ⟨hAsub, hAcard⟩ : A ⊆ S.image left ∧ (A.biUnion nbr).card < A.card := by
      have := Finset.mem_filter.mp hAbad
      exact this.2
    have hA2 : 2 ≤ A.card := by
      by_contra hlt
      interval_cases h : A.card
      · omega
      · obtain ⟨x, hAx⟩ := Finset.card_eq_one.mp h
        subst hAx
        have hxim : x ∈ S.image left := hAsub (Finset.mem_singleton_self x)
        obtain ⟨e, heS, hex⟩ := Finset.mem_image.mp hxim
        have : (nbr x).Nonempty :=
          ⟨right e, Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨heS, hex⟩, rfl⟩⟩
        have hcard : 1 ≤ (({x} : Finset U).biUnion nbr).card := by
          rw [Finset.singleton_biUnion]
          exact Finset.card_pos.mpr this
        omega
    obtain ⟨x, hx⟩ : A.Nonempty := Finset.card_pos.mp (by omega)
    set A' : Finset U := A.erase x with hA'
    have hA'card : A'.card = A.card - 1 := Finset.card_erase_of_mem hx
    have hA'sub : A' ⊆ A := Finset.erase_subset _ _
    have hA'ne : A'.Nonempty := Finset.card_pos.mp (by omega)
    have hall' : ∀ B ⊆ A', B.card ≤ (B.biUnion nbr).card := by
      intro B hB
      by_contra hlt
      push Not at hlt
      have hBbad : B ∈ bad := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hB.trans hA'sub).trans hAsub, hlt⟩
      have := hAmin B hBbad
      have hBcard : B.card ≤ A'.card := Finset.card_le_card hB
      omega
    obtain ⟨M, hMS, hMne, hM, hcov, hleftmem, himgsub, hcardge⟩ :=
      hall_matching left right S A' hA'ne hall'
    have hNsub : A'.biUnion nbr ⊆ A.biUnion nbr := Finset.biUnion_subset_biUnion_of_subset_left _
        hA'sub
    have hNcard : (A'.biUnion nbr).card ≤ (M.image right).card := by
      have := Finset.card_le_card hNsub
      omega
    have heq : M.image right = A'.biUnion nbr :=
      Finset.eq_of_subset_of_card_le himgsub hNcard
    refine ⟨M, hMS, hMne, hM, Or.inr ?_⟩
    rintro e heS ⟨f, hfM, hfl⟩
    have hxA' : left e ∈ A' := hfl ▸ hleftmem f hfM
    have : right e ∈ A'.biUnion nbr :=
      Finset.mem_biUnion.mpr ⟨left e, hxA',
        Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨heS, rfl⟩, rfl⟩⟩
    rw [← heq] at this
    obtain ⟨f', hf', hf'r⟩ := Finset.mem_image.mp this
    exact ⟨f', hf', hf'r⟩
end GalvinMultigraph.Local
