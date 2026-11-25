-- Prove2me | solution 1 for ConjCoord.Proof.card_eq_two_mul_filter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:47:19.876327+00:00
-- url     : https://prove2.me/submissions/a4ab5e2b-cc96-445c-ab48-392ef416c62d

module
public import Definitions.Def_ConjCoord_Defs
public import Definitions.Def_ConjCoord_Reps

set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof
namespace ConjCoord.Proof
theorem _root_.solution {α : Type*} (S : Finset α) (σ : α → α) (P : α → Prop)
    [DecidablePred P] (hS : ∀ x ∈ S, σ x ∈ S) (hσ : ∀ x ∈ S, σ (σ x) = x)
    (hP : ∀ x ∈ S, P (σ x) ↔ ¬ P x) : S.card = 2 * (S.filter P).card := by
  rw [← card_filter_add_card_filter_not (s := S) (p := P)]
  have : (S.filter fun x => ¬ P x).card = (S.filter P).card := by
    refine card_nbij' σ σ ?_ ?_ ?_ ?_
    · intro x hx
      simp only [mem_coe, mem_filter] at hx ⊢
      exact ⟨hS x hx.1, (hP x hx.1).mpr hx.2⟩
    · intro x hx
      simp only [mem_coe, mem_filter] at hx ⊢
      refine ⟨hS x hx.1, fun h => ?_⟩
      exact ((hP x hx.1).mp h) hx.2
    · intro x hx; simp only [mem_coe, mem_filter] at hx; exact hσ x hx.1
    · intro x hx; simp only [mem_coe, mem_filter] at hx; exact hσ x hx.1
  omega
end ConjCoord.Proof
