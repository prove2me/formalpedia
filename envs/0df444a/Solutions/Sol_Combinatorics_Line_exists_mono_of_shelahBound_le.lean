-- Prove2me | solution 1 for Combinatorics.Line.exists_mono_of_shelahBound_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:52:15.061933+00:00
-- url     : https://prove2.me/submissions/4a532bb2-dbb4-42d3-8b63-7575d44b2f84

module
public import Mathlib.Combinatorics.HalesJewett
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.SetTheory.Cardinal.NatCard
public import Definitions.Def_ShelahHalesJewett_Line
public import Definitions.Def_ShelahHalesJewett_HalesJewett
public import Theorems.Thm_Combinatorics_Line_exists_mono_of_card_eq_shelahBound
public import Theorems.Thm_Combinatorics_Subspace_compLine_apply
attribute [local simp] Combinatorics.Subspace.compLine_apply



set_option autoImplicit true
@[expose] public section
public section
open Combinatorics
open Combinatorics.Line
variable {α κ ι : Type*} [Fintype α] [Fintype κ] [Fintype ι]
namespace Combinatorics.Line
theorem _root_.solution [Nonempty α]
    (h : shelahBound (Fintype.card α) (Fintype.card κ) ≤ Fintype.card ι) (C : (ι → α) → κ) :
    ∃ l : Line α ι, l.IsMono C := by
  let e : Fin (shelahBound (Fintype.card α) (Fintype.card κ)) ⊕
      Fin (Fintype.card ι - shelahBound (Fintype.card α) (Fintype.card κ)) ≃ ι :=
    Fintype.equivOfCardEq (by simp [Nat.add_sub_cancel' h])
  let a : α := Classical.arbitrary α
  obtain ⟨l, c, hc⟩ := exists_mono_of_card_eq_shelahBound (by simp)
    fun v : Fin (shelahBound (Fintype.card α) (Fintype.card κ)) → α ↦
      C (Sum.elim v (fun _ ↦ a) ∘ e.symm)
  refine ⟨(l.horizontal fun _ ↦ a).reindex e, c, ?_⟩
  intro x
  rw [reindex_apply, horizontal_apply]
  exact hc x
end Combinatorics.Line
