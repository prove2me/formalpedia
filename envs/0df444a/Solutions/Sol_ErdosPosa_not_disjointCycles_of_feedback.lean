-- Prove2me | solution 1 for ErdosPosa.not_disjointCycles_of_feedback
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:32:37.290846+00:00
-- url     : https://prove2.me/submissions/55c94990-13a3-4666-81ce-6831ae3c384f

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPMain
public import Definitions.Def_ErdosPosaLib_ErdosPosa
public import Theorems.Thm_ErdosPosa_cyc_mono
public import Theorems.Thm_ErdosPosa_not_isAcyclic_induce_iff
public import Theorems.Thm_ErdosPosa_restr_adj
attribute [local simp] ErdosPosa.restr_adj



set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
universe u
namespace ErdosPosa
theorem _root_.solution {V : Type u} [Finite V] (G : SimpleGraph V) {X : Set V}
    (hX : IsFeedbackSet G X) : ¬ HasDisjointCycles G (X.ncard + 1) := by
  rintro ⟨S, hS, hcyc⟩
  have hmeet : ∀ i, ∃ x ∈ S i, x ∈ X := by
    intro i
    by_contra hcon
    push Not at hcon
    have h1 := not_isAcyclic_induce_iff.1 (hcyc i)
    exact not_isAcyclic_induce_iff.2 (cyc_mono h1 le_rfl (fun x hx => hcon x hx)) hX
  choose f hfS hfX using hmeet
  have hinj : Function.Injective (fun i => (⟨f i, hfX i⟩ : X)) := by
    intro i j hij
    by_contra hne
    have hfij : f i = f j := congrArg Subtype.val hij
    exact Set.disjoint_left.1 (hS hne) (hfS i) (hfij ▸ hfS j)
  have := Nat.card_le_card_of_injective _ hinj
  simp only [Nat.card_coe_set_eq, Nat.card_eq_fintype_card, Fintype.card_fin] at this
  omega
end ErdosPosa
