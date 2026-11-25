-- Prove2me | solution 1 for ConjCoord.Proof.one_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:48:15.712741+00:00
-- url     : https://prove2.me/submissions/917201a5-42ae-4c26-98ff-be876da7a738

module
public import Definitions.Def_ConjCoord_Defs
public import Definitions.Def_ConjCoord_Reps
public import Theorems.Thm_ConjCoord_Proof_sq_mod4

set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof
variable {n : ℕ}
namespace ConjCoord.Proof
theorem _root_.solution (hn : n % 2 = 1) {X U V : ℤ} (h : X ^ 2 + U ^ 2 + V ^ 2 = 2 * n) :
    (Even X ∧ ¬ Even U ∧ ¬ Even V) ∨ (¬ Even X ∧ Even U ∧ ¬ Even V) ∨
      (¬ Even X ∧ ¬ Even U ∧ Even V) := by
  simp only [Int.not_even_iff_odd]
  rcases sq_mod4 X with ⟨hX, hX'⟩ | ⟨hX, hX'⟩ <;>
  rcases sq_mod4 U with ⟨hU, hU'⟩ | ⟨hU, hU'⟩ <;>
  rcases sq_mod4 V with ⟨hV, hV'⟩ | ⟨hV, hV'⟩ <;>
  first
    | exact Or.inl ⟨hX, hU, hV⟩
    | exact Or.inr (Or.inl ⟨hX, hU, hV⟩)
    | exact Or.inr (Or.inr ⟨hX, hU, hV⟩)
    | (exfalso; omega)
end ConjCoord.Proof
