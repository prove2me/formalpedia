-- Prove2me | solution 1 for ConjCoord.Proof.tCoeff_check
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:54:37.995746+00:00
-- url     : https://prove2.me/submissions/a3659ab1-01b3-4560-9d04-245489cdfc57

module
public import Definitions.Def_ConjCoord_Defs
public import Definitions.Def_ConjCoord_Compute
public import Theorems.Thm_ConjCoord_Proof_tCoeff_eq_tCoeffL
public import Theorems.Thm_ConjCoord_Proof_tCoeffL_check

set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof
namespace ConjCoord.Proof
theorem _root_.solution (m : ℕ) (hm : m ≤ 512) : (64 : ℤ) ∣ tCoeff m := by
  rw [tCoeff_eq_tCoeffL]; exact tCoeffL_check m (by omega)
end ConjCoord.Proof
