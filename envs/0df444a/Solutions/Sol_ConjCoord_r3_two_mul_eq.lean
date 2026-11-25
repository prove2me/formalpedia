-- Prove2me | solution 1 for ConjCoord.r3_two_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:56:07.641606+00:00
-- url     : https://prove2.me/submissions/088d8db7-6313-4396-8836-e3382561038a

module
public import Definitions.Def_ConjCoord
public import Definitions.Def_ConjCoord_Solution
public import Theorems.Thm_ConjCoord_Proof_r3_two_mul_eq


set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord
namespace ConjCoord
theorem _root_.solution {n : ℕ} (hn : n % 2 = 1) : r3 (2 * n) = 3 * reps 1 1 2 n :=
  Proof.r3_two_mul_eq hn
end ConjCoord
