-- Prove2me | solution 1 for ConjCoord.Proof.tCoeff_eq_tCoeffL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:53:41.162153+00:00
-- url     : https://prove2.me/submissions/2ff29638-d3ca-405b-ad54-26231f0ffeb0

module
public import Definitions.Def_ConjCoord_Defs
public import Definitions.Def_ConjCoord_Compute
public import Theorems.Thm_ConjCoord_Proof_reps_eq_cntL
public import Theorems.Thm_ConjCoord_Proof_gCount_eq_cntL

set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof
namespace ConjCoord.Proof
theorem _root_.solution (m : ℕ) : tCoeff m = tCoeffL m := by
  unfold tCoeff tCoeffL
  rw [reps_eq_cntL 1 2 4 m (by norm_num) (by norm_num) (by norm_num),
    reps_eq_cntL 1 2 2 m (by norm_num) (by norm_num) (by norm_num), gCount_eq_cntL]
end ConjCoord.Proof
