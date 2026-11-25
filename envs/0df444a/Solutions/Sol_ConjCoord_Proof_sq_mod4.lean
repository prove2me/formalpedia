-- Prove2me | solution 1 for ConjCoord.Proof.sq_mod4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:46:42.522212+00:00
-- url     : https://prove2.me/submissions/256e6c07-aa16-4ef1-adf5-621b9b0a3d94

module
public import Definitions.Def_ConjCoord_Defs
public import Definitions.Def_ConjCoord_Reps

set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof
namespace ConjCoord.Proof
theorem _root_.solution (x : ℤ) : (Even x ∧ x ^ 2 % 4 = 0) ∨ (Odd x ∧ x ^ 2 % 4 = 1) := by
  rcases Int.even_or_odd x with ⟨r, rfl⟩ | ⟨r, rfl⟩
  · left; refine ⟨⟨r, rfl⟩, ?_⟩; ring_nf; omega
  · right; refine ⟨⟨r, rfl⟩, ?_⟩; ring_nf; omega
end ConjCoord.Proof
