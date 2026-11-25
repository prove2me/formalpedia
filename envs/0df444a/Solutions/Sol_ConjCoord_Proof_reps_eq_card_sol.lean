-- Prove2me | solution 1 for ConjCoord.Proof.reps_eq_card_sol
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:47:04.301895+00:00
-- url     : https://prove2.me/submissions/6da981b7-e750-4322-8ed0-d52711345add

module
public import Definitions.Def_ConjCoord_Defs
public import Definitions.Def_ConjCoord_Reps

set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof
namespace ConjCoord.Proof
theorem _root_.solution (a b c n : ℕ) : reps a b c n = (sol a b c n).card := rfl
end ConjCoord.Proof
