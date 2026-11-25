-- Prove2me | solution 1 for ConjCoord.Proof.phi_check
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:56:40.991795+00:00
-- url     : https://prove2.me/submissions/33ef3084-f615-4a83-bfa6-6c57615f8d7c

module
public import Definitions.Def_ConjCoord_Compute
public import Definitions.Def_ConjCoord_TwoSquares
public import Definitions.Def_ConjCoord_Main
public import Theorems.Thm_ConjCoord_Proof_phi_dvd_of
public import Theorems.Thm_ConjCoord_Proof_tCoeff_check


set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof
namespace ConjCoord.Proof
theorem _root_.solution (n : ℕ) (hn : n ≤ 512) : (256 : ℤ) ∣ phi n :=
  phi_dvd_of fun m hm => tCoeff_check m (hm.trans hn)
end ConjCoord.Proof
