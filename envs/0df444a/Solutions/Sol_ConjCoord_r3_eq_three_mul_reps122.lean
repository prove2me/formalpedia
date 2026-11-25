-- Prove2me | solution 1 for ConjCoord.r3_eq_three_mul_reps122
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:56:05.280253+00:00
-- url     : https://prove2.me/submissions/e352db97-0e84-4076-a876-af35ac753b5b

module
public import Definitions.Def_ConjCoord
public import Definitions.Def_ConjCoord_Solution
public import Theorems.Thm_ConjCoord_Proof_r3_eq_three_mul_reps122


set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord
namespace ConjCoord
theorem _root_.solution {n : ℕ} (hn : n % 4 = 1) : r3 n = 3 * reps 1 2 2 n :=
  Proof.r3_eq_three_mul_reps122 hn
end ConjCoord
