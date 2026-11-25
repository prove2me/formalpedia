-- Prove2me | solution 1 for ConjCoord.Proof.card_eq_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:47:06.360169+00:00
-- url     : https://prove2.me/submissions/a4a45ffc-a8d2-48d2-a10a-f1c50b86e312

module
public import Definitions.Def_ConjCoord_Defs
public import Definitions.Def_ConjCoord_Reps

set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof
namespace ConjCoord.Proof
theorem _root_.solution {α : Type*} (S : Finset α) (P Q R : α → Prop) [DecidablePred P]
    [DecidablePred Q] [DecidablePred R]
    (h : ∀ x ∈ S, (P x ∧ ¬ Q x ∧ ¬ R x) ∨ (¬ P x ∧ Q x ∧ ¬ R x) ∨ (¬ P x ∧ ¬ Q x ∧ R x)) :
    S.card = (S.filter P).card + (S.filter Q).card + (S.filter R).card := by
  rw [card_filter, card_filter, card_filter, card_eq_sum_ones, ← sum_add_distrib,
    ← sum_add_distrib]
  refine sum_congr rfl fun x hx => ?_
  rcases h x hx with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> simp [h1, h2, h3]
end ConjCoord.Proof
