-- Prove2me | solution 1 for ConjCoord.Proof.phi_dvd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:57:52.819887+00:00
-- url     : https://prove2.me/submissions/04a56379-0cb1-40b4-bf8d-3582ccbce33c

module
public import Definitions.Def_ConjCoord_Compute
public import Definitions.Def_ConjCoord_TwoSquares
public import Definitions.Def_ConjCoord_Main
public import Theorems.Thm_ConjCoord_Proof_sturm_iter
public import Theorems.Thm_ConjCoord_Proof_phi_check

set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof
namespace ConjCoord.Proof
theorem _root_.solution (S : SturmInput phi 512) (n : ℕ) : (256 : ℤ) ∣ phi n := by
  have := sturm_iter S 8 phi S.mem (fun n hn => by norm_num; exact phi_check n hn) n
  norm_num at this; exact this
end ConjCoord.Proof
