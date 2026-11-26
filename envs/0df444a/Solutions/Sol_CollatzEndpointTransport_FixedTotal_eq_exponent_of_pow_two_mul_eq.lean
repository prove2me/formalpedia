-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.eq_exponent_of_pow_two_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:25:47.806853+00:00
-- url     : https://prove2.me/submissions/d1e96824-4872-4f64-8351-abb76e957901

import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalComposition
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_cons

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {a b x y : ℕ}
    (hx : x % 2 = 1) (hy : y % 2 = 1)
    (h : 2 ^ a * x = 2 ^ b * y) :
    a = b := by
  have hx0 : x ≠ 0 := by
    intro hzero
    simp [hzero] at hx
  have hy0 : y ≠ 0 := by
    intro hzero
    simp [hzero] at hy
  have hxdvd : ¬2 ∣ x := by
    rw [Nat.dvd_iff_mod_eq_zero]
    omega
  have hydvd : ¬2 ∣ y := by
    rw [Nat.dvd_iff_mod_eq_zero]
    omega
  have hvx : padicValNat 2 x = 0 :=
    padicValNat.eq_zero_of_not_dvd hxdvd
  have hvy : padicValNat 2 y = 0 :=
    padicValNat.eq_zero_of_not_dvd hydvd
  have hv := congrArg (padicValNat 2) h
  rw [padicValNat.mul (pow_ne_zero _ (by norm_num)) hx0,
    padicValNat.mul (pow_ne_zero _ (by norm_num)) hy0,
    padicValNat.prime_pow, padicValNat.prime_pow, hvx, hvy,
    add_zero, add_zero] at hv
  exact hv
end CollatzEndpointTransport.FixedTotal
