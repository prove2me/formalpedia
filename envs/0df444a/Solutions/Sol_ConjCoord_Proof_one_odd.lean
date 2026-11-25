-- Prove2me | solution 1 for ConjCoord.Proof.one_odd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:48:13.217386+00:00
-- url     : https://prove2.me/submissions/3b3f01ec-2d26-4db0-9152-4231edb156d7

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
theorem _root_.solution (hn : n % 4 = 1) {X U V : ℤ} (h : X ^ 2 + U ^ 2 + V ^ 2 = n) :
    (Odd X ∧ ¬ Odd U ∧ ¬ Odd V) ∨ (¬ Odd X ∧ Odd U ∧ ¬ Odd V) ∨
      (¬ Odd X ∧ ¬ Odd U ∧ Odd V) := by
  simp only [Int.not_odd_iff_even]
  rcases sq_mod4 X with ⟨hX, hX'⟩ | ⟨hX, hX'⟩ <;>
  rcases sq_mod4 U with ⟨hU, hU'⟩ | ⟨hU, hU'⟩ <;>
  rcases sq_mod4 V with ⟨hV, hV'⟩ | ⟨hV, hV'⟩ <;>
  first
    | exact Or.inl ⟨hX, hU, hV⟩
    | exact Or.inr (Or.inl ⟨hX, hU, hV⟩)
    | exact Or.inr (Or.inr ⟨hX, hU, hV⟩)
    | (exfalso; omega)
end ConjCoord.Proof
