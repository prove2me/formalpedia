-- Prove2me | solution 1 for Combinatorics.Subspace.exists_insensitive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:50:55.303593+00:00
-- url     : https://prove2.me/submissions/5e2bcea6-bb89-4133-9576-c5f7626a2beb

module
public import Mathlib.Combinatorics.HalesJewett
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.SetTheory.Cardinal.NatCard
public import Definitions.Def_ShelahHalesJewett_Line
public import Definitions.Def_ShelahHalesJewett_HalesJewett
public import Theorems.Thm_Combinatorics_Line_exists_map_eq_of_card_le
public import Theorems.Thm_Combinatorics_Subspace_compLine_apply
attribute [local simp] Combinatorics.Subspace.compLine_apply



set_option autoImplicit true
@[expose] public section
public section
open Combinatorics
open Combinatorics.Subspace
namespace Combinatorics.Subspace
theorem _root_.solution (α : Type) [Finite α] (a b : α) (η : Type) [Finite η]
    (κ : Type) [Finite κ] :
    ∃ (ι : Type) (_ : Fintype ι),
      Fintype.card ι = insensitiveBound (Nat.card α) (Nat.card η) (Nat.card κ) ∧
      ∀ C : (ι → α) → κ, ∃ V : Subspace η α ι,
        ∀ x y : η → α, (∀ e, x e = y e ∨ x e = a ∧ y e = b) → C (V x) = C (V y) := by
  induction η using Finite.induction_empty_option generalizing κ with
  | @of_equiv η η' e ih =>
    obtain ⟨ι, _, hι, h⟩ := ih κ
    refine ⟨ι, ‹_›, Nat.card_congr e ▸ hι, ?_⟩
    intro C
    obtain ⟨V, hV⟩ := h C
    refine ⟨V.reindex e (.refl α) (.refl ι), ?_⟩
    intro x y hxy
    have key (z : η' → α) : V.reindex e (.refl α) (.refl ι) z = V (z ∘ e) := by
      ext
      simp
    rw [key, key]
    apply hV
    intro e'
    exact hxy (e e')
  | h_empty =>
    refine ⟨Empty, inferInstance, by simp [insensitiveBound], ?_⟩
    intro C
    refine ⟨⟨fun i ↦ i.elim, fun e ↦ e.elim⟩, ?_⟩
    intro x y _
    rw [Subsingleton.elim x y]
  | h_option ih =>
    obtain ⟨ι, _, hι, h⟩ := ih (α → κ)
    refine ⟨ι ⊕ Fin (Nat.card ((ι → α) → κ)), inferInstance,
      by simp [insensitiveBound, Nat.card_fun, hι], ?_⟩
    intro C
    obtain ⟨l, hl⟩ := Line.exists_map_eq_of_card_le le_rfl a b
      fun (u : Fin (Nat.card ((ι → α) → κ)) → α) (w : ι → α) ↦ C (Sum.elim w u)
    obtain ⟨V, hV⟩ := h fun w x ↦ C (Sum.elim w (l x))
    refine ⟨V.prodLine l, ?_⟩
    intro x y hxy
    rw [prodLine_apply, prodLine_apply]
    apply (congrFun (hV (x ∘ some) (y ∘ some) fun e ↦ hxy (some e)) (x none)).trans
    grind [congrFun hl (V (y ∘ some))]
end Combinatorics.Subspace
