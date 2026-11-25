-- Prove2me | solution 1 for ConjCoord.Proof.neg_cond
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:49:55.936046+00:00
-- url     : https://prove2.me/submissions/7102cb8b-a17c-4ed6-9031-df7997b14a92

module
public import Definitions.Def_ConjCoord_Reps
public import Definitions.Def_ConjCoord_TwoSquares

set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof
namespace ConjCoord.Proof
theorem _root_.solution (β : ℤ) : ((-β) % 16 = 6 ∨ (-β) % 16 = 10) ↔ (β % 16 = 6 ∨ β % 16 = 10) := by
  omega
end ConjCoord.Proof
