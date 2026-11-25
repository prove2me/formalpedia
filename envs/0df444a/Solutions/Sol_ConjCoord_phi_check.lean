-- Prove2me | solution 1 for ConjCoord.phi_check
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:58:55.084985+00:00
-- url     : https://prove2.me/submissions/032c1476-5f98-46cf-ac15-be2d16477ce6

module
public import Definitions.Def_ConjCoord
public import Definitions.Def_ConjCoord_Solution
public import Theorems.Thm_ConjCoord_Proof_phi_check


set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord
namespace ConjCoord
theorem _root_.solution (n : ℕ) (hn : n ≤ 512) : (256 : ℤ) ∣ phi n :=
  Proof.phi_check n hn
end ConjCoord
