-- Prove2me | solution 1 for GalvinMultigraph.Local.saturating_matching_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:02:08.114924+00:00
-- url     : https://prove2.me/submissions/56db4387-f508-4afb-a0fd-d4619f7bea11

module
public import Definitions.Def_GalvinMultigraph_Local_Stable
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.Set
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Group.Action.Defs
public import Definitions.Def_GalvinMultigraph_Local_Konig
public import Theorems.Thm_GalvinMultigraph_Local_card_filter_left_mem
public import Theorems.Thm_GalvinMultigraph_Local_card_filter_right_mem

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
theorem _root_.solution (left : E → U) (right : E → R) (S : Finset E) (Δ : ℕ) (hΔ : 0 < Δ)
    (hR : ∀ r, degROn right S r ≤ Δ) :
    ∃ M : Finset E, M ⊆ S ∧ IsMatchingOn left right M ∧
      ∀ u, degLOn left S u = Δ → ∃ e ∈ M, left e = u := by
  classical
  set T0 : Finset U := Finset.univ.filter (fun u => degLOn left S u = Δ) with hT0
  set nbr : U → Finset R := fun u => (S.filter fun e => left e = u).image right with hnbr
  have hall : ∀ A : Finset ↥T0, A.card ≤ (A.biUnion (fun u => nbr u.val)).card := by
    intro A
    set AU : Finset U := A.image Subtype.val with hAU
    set B : Finset R := A.biUnion (fun u => nbr u.val) with hB
    have hAUcard : AU.card = A.card := Finset.card_image_of_injective _ Subtype.val_injective
    have h1 : (S.filter fun e => left e ∈ AU).card = Δ * A.card := by
      rw [card_filter_left_mem left S AU]
      have : ∀ u ∈ AU, degLOn left S u = Δ := by
        intro u hu
        obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hu
        exact (Finset.mem_filter.mp v.2).2
      rw [Finset.sum_congr rfl this, Finset.sum_const, smul_eq_mul, hAUcard, mul_comm]
    have hsub : (S.filter fun e => left e ∈ AU) ⊆ (S.filter fun e => right e ∈ B) := by
      intro e he
      simp only [Finset.mem_filter] at he ⊢
      refine ⟨he.1, ?_⟩
      obtain ⟨u, huA, hu⟩ := Finset.mem_image.mp he.2
      exact Finset.mem_biUnion.mpr ⟨u, huA,
        Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨he.1, hu.symm⟩, rfl⟩⟩
    have h2 : (S.filter fun e => right e ∈ B).card ≤ Δ * B.card := by
      rw [card_filter_right_mem right S B]
      calc ∑ r ∈ B, degROn right S r ≤ ∑ _r ∈ B, Δ := Finset.sum_le_sum fun r _ => hR r
        _ = Δ * B.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    have : Δ * A.card ≤ Δ * B.card := by
      calc Δ * A.card = (S.filter fun e => left e ∈ AU).card := h1.symm
        _ ≤ (S.filter fun e => right e ∈ B).card := Finset.card_le_card hsub
        _ ≤ Δ * B.card := h2
    exact Nat.le_of_mul_le_mul_left this hΔ
  obtain ⟨f, hfinj, hf⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective (fun u : ↥T0 => nbr u.val)).mp hall
  have hex : ∀ u : ↥T0, ∃ e, e ∈ S ∧ left e = u.val ∧ right e = f u := by
    intro u
    obtain ⟨e, he, hre⟩ := Finset.mem_image.mp (hf u)
    exact ⟨e, (Finset.mem_filter.mp he).1, (Finset.mem_filter.mp he).2, hre⟩
  choose g hgS hgl hgr using hex
  refine ⟨Finset.image g Finset.univ, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp he
    exact hgS u
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
    have huT : u ∈ T0 := Finset.mem_filter.mpr ⟨Finset.mem_univ u, hu⟩
    exact ⟨g ⟨u, huT⟩, Finset.mem_image.mpr ⟨⟨u, huT⟩, Finset.mem_univ _, rfl⟩, hgl ⟨u, huT⟩⟩
end GalvinMultigraph.Local
