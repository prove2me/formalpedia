-- Prove2me | solution 1 for ConjCoord.Proof.gCount_eq_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:50:48.160435+00:00
-- url     : https://prove2.me/submissions/9cc6766f-9a1c-4716-b3ea-aa39a96fe0a8

module
public import Definitions.Def_ConjCoord_Reps
public import Definitions.Def_ConjCoord_TwoSquares

set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof
namespace ConjCoord.Proof
theorem _root_.solution (m : ℕ) : gCount m = (gset m).card := rfl
end ConjCoord.Proof
