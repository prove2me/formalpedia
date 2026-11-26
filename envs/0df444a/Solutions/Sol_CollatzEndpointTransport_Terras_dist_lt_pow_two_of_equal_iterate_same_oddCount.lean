-- Prove2me | solution 1 for CollatzEndpointTransport.Terras.dist_lt_pow_two_of_equal_iterate_same_oddCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:58:12.417936+00:00
-- url     : https://prove2.me/submissions/8f4a143f-846a-4e57-ac3b-17ad667cb2d9

import Definitions.Def_CollatzEndpointTransport_Common_TerrasAffineIterate
import Definitions.Def_CollatzEndpointTransport_Common_TerrasIntegerAffine
import Theorems.Thm_CollatzEndpointTransport_Terras_integerCorrection_zero
import Theorems.Thm_CollatzEndpointTransport_Terras_sub_lt_pow_two_of_equal_iterate_same_oddCount
attribute [local simp] CollatzEndpointTransport.Terras.integerCorrection_zero

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset
namespace CollatzEndpointTransport.Terras
theorem _root_.solution
    {d k n m : ℕ}
    (hnk : oddCount d n = k)
    (hmk : oddCount d m = k)
    (hout : (T^[d]) n = (T^[d]) m) :
    n.dist m < 2 ^ d := by
  rcases lt_trichotomy n m with hlt | heq | hgt
  · rw [Nat.dist_eq_sub_of_le (Nat.le_of_lt hlt)]
    exact sub_lt_pow_two_of_equal_iterate_same_oddCount
      hlt hnk hmk hout
  · subst m
    simp [Nat.dist, pow_pos (by norm_num : 0 < (2 : ℕ)) d]
  · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le (Nat.le_of_lt hgt)]
    exact sub_lt_pow_two_of_equal_iterate_same_oddCount
      hgt hmk hnk hout.symm
end CollatzEndpointTransport.Terras
