-- Prove2me | solution 1 for ConjCoord.tCoeff_check
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:56:25.380996+00:00
-- url     : https://prove2.me/submissions/6c773304-02eb-453c-8226-09930815323b

module
public import Definitions.Def_ConjCoord
public import Definitions.Def_ConjCoord_Solution
public import Theorems.Thm_ConjCoord_Proof_tCoeff_check


set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord
namespace ConjCoord
theorem _root_.solution (m : ℕ) (hm : m ≤ 512) : (64 : ℤ) ∣ tCoeff m :=
  Proof.tCoeff_check m hm
end ConjCoord
