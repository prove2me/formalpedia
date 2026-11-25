-- Prove2me | solution 1 for ConjCoord.tCoeff_dvd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:01:10.756474+00:00
-- url     : https://prove2.me/submissions/a306bd95-109b-4b52-9b40-b080497f1fda

module
public import Definitions.Def_ConjCoord
public import Definitions.Def_ConjCoord_Solution
public import Theorems.Thm_ConjCoord_Proof_tCoeff_dvd


set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord
namespace ConjCoord
theorem _root_.solution (S : SturmInput phi 512) (m : ℕ) : (64 : ℤ) ∣ tCoeff m :=
  Proof.tCoeff_dvd S m
end ConjCoord
