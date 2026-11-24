-- Prove2me | solution 1 for Combinatorics.Line.exists_mono_of_card_eq_shelahBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:51:41.03187+00:00
-- url     : https://prove2.me/submissions/6859c9d9-a31b-4812-8aad-c1613ef10fbf

module
public import Mathlib.Combinatorics.HalesJewett
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.SetTheory.Cardinal.NatCard
public import Definitions.Def_ShelahHalesJewett_Line
public import Definitions.Def_ShelahHalesJewett_HalesJewett
public import Theorems.Thm_Combinatorics_Subspace_exists_insensitive
public import Theorems.Thm_Combinatorics_Subspace_compLine_apply
attribute [local simp] Combinatorics.Subspace.compLine_apply


section
@[expose] public section
namespace Combinatorics
namespace Subspace
end Subspace
namespace Line
private lemma exists_mono_shelahBound' (α : Type) [Finite α] (κ : Type) [Finite κ] :
    ∃ (ι : Type) (_ : Fintype ι), Fintype.card ι = shelahBound (Nat.card α) (Nat.card κ) ∧
      ∀ C : (ι → α) → κ, ∃ l : Line α ι, l.IsMono C := by
  induction α using Finite.induction_empty_option generalizing κ with
  | @of_equiv α α' e ih =>
    obtain ⟨ι, _, hι, h⟩ := ih κ
    refine ⟨ι, ‹_›, Nat.card_congr e ▸ hι, ?_⟩
    intro C
    obtain ⟨l, c, hc⟩ := h fun v ↦ C (e ∘ v)
    refine ⟨l.map e, c, ?_⟩
    intro x
    rw [← e.apply_symm_apply x, map_apply]
    exact hc _
  | h_empty =>
    rcases isEmpty_or_nonempty κ with hκ | hκ
    · refine ⟨Empty, inferInstance, by simp [shelahBound], ?_⟩
      intro C
      exact isEmptyElim (C isEmptyElim)
    · refine ⟨Unit, inferInstance, by simp [shelahBound, Nat.succ_le_iff], ?_⟩
      intro C
      exact ⟨default, Classical.arbitrary κ, isEmptyElim⟩
  | @h_option α _ ih =>
    rcases isEmpty_or_nonempty α with hα | hα
    · refine ⟨Unit, inferInstance, by simp [shelahBound], ?_⟩
      intro C
      refine ⟨diagonal _ Unit, C (diagonal _ Unit none), ?_⟩
      intro x
      rw [Subsingleton.elim x none]
    obtain ⟨ι', _, hι', h'⟩ := ih κ
    obtain ⟨ι, _, hι, h⟩ :=
      Subspace.exists_insensitive (Option α) none (some (Classical.arbitrary α)) ι' κ
    refine ⟨ι, ‹_›, ?_, ?_⟩
    · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.card_pos (α := α)).ne'
      rw [hι, Finite.card_option, hk, shelahBound, Nat.card_eq_fintype_card (α := ι'), hι', hk]
    intro C
    obtain ⟨V, hV⟩ := h C
    obtain ⟨l, c, hc⟩ := h' fun w ↦ C (V (some ∘ w))
    refine ⟨V.compLine (l.map some), c, ?_⟩
    intro x
    rw [Subspace.compLine_apply]
    have hsome (x' : α) : C (V (l.map some (some x'))) = c := by simpa using hc x'
    rcases x with _ | x
    · rw [← hsome (Classical.arbitrary α)]
      apply hV
      intro e
      cases he : l.idxFun e <;> simp [map, he]
    · exact hsome x
variable {α κ ι : Type*} [Fintype α] [Fintype κ] [Fintype ι]
end Line
end Combinatorics
end
end

set_option autoImplicit true
@[expose] public section
public section
open Combinatorics
open Combinatorics.Line
variable {α κ ι : Type*} [Fintype α] [Fintype κ] [Fintype ι]
namespace Combinatorics.Line
theorem _root_.solution
    (h : Fintype.card ι = shelahBound (Fintype.card α) (Fintype.card κ)) (C : (ι → α) → κ) :
    ∃ l : Line α ι, l.IsMono C := by
  obtain ⟨ι₀, _, hι₀, h₀⟩ :=
    exists_mono_shelahBound' (Fin (Fintype.card α)) (Fin (Fintype.card κ))
  rw [Nat.card_fin, Nat.card_fin, ← h] at hι₀
  let eα := Fintype.equivFin α
  let eκ := Fintype.equivFin κ
  let eι := Fintype.equivOfCardEq hι₀
  obtain ⟨l, c, hc⟩ := h₀ fun v ↦ eκ (C (eα.symm ∘ v ∘ eι.symm))
  refine ⟨(l.map eα.symm).reindex eι, eκ.symm c, ?_⟩
  intro x
  rw [reindex_apply, ← eα.symm_apply_apply x, map_apply]
  exact eκ.eq_symm_apply.2 (hc (eα x))
end Combinatorics.Line
