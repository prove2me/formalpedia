-- Prove2me | solution 1 for ConjCoord.Proof.sq_mod16_ne5
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:49:38.107956+00:00
-- url     : https://prove2.me/submissions/4a082a93-a7e0-47da-84ce-029ccfda7e69

module
public import Definitions.Def_ConjCoord_Reps
public import Definitions.Def_ConjCoord_TwoSquares

set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof
namespace ConjCoord.Proof
theorem _root_.solution (x : ℤ) : x ^ 2 % 16 ≠ 5 := by
  have h := Int.emod_add_mul_ediv x 16
  have h0 : 0 ≤ x % 16 := Int.emod_nonneg x (by norm_num)
  have h1 : x % 16 < 16 := Int.emod_lt_of_pos x (by norm_num)
  generalize x % 16 = r at h h0 h1
  generalize x / 16 = q at h
  subst h
  interval_cases r <;> ring_nf <;> omega
end ConjCoord.Proof
