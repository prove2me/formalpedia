-- Prove2me | solution 1 for ConjCoord.phi_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:55:55.977577+00:00
-- url     : https://prove2.me/submissions/20aee3ec-fa2f-4fb7-9272-4ef81a3b5732

module
public import Definitions.Def_ConjCoord
public import Definitions.Def_ConjCoord_Solution
public import Theorems.Thm_ConjCoord_Proof_phi_eq


set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord
namespace ConjCoord
theorem _root_.solution (n : ℕ) :
    phi n = 4 * (tCoeff n + ∑ k ∈ range n,
      2 * (if (k + 1) ^ 2 ≤ n then tCoeff (n - (k + 1) ^ 2) else 0)) :=
  Proof.phi_eq n
end ConjCoord
