-- Prove2me | solution 1 for ConjCoord.phi_dvd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:59:44.090322+00:00
-- url     : https://prove2.me/submissions/a71fb543-cf8f-4f1a-a27c-813e7f7eb10f

module
public import Definitions.Def_ConjCoord
public import Definitions.Def_ConjCoord_Solution
public import Theorems.Thm_ConjCoord_Proof_phi_dvd


set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord
namespace ConjCoord
theorem _root_.solution (S : SturmInput phi 512) (n : ℕ) : (256 : ℤ) ∣ phi n :=
  Proof.phi_dvd S n
end ConjCoord
