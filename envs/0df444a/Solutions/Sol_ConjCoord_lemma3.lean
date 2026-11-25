-- Prove2me | solution 1 for ConjCoord.lemma3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:56:57.80023+00:00
-- url     : https://prove2.me/submissions/a8c99826-4c4f-4eec-96cc-a9392f459313

module
public import Definitions.Def_ConjCoord
public import Definitions.Def_ConjCoord_Solution
public import Theorems.Thm_ConjCoord_Proof_lemma3


set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord
namespace ConjCoord
theorem _root_.solution {p : ℕ} (hp : p % 16 = 5) :
    r3 p = 3 * reps 1 2 2 p ∧ r3 (2 * p) = 6 * reps 1 2 4 p :=
  Proof.lemma3 hp
end ConjCoord
