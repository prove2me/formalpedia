-- Prove2me | solution 1 for CollatzEndpointTransport.Terras.iterate_lt_three_pow_mul_remaining
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:24:29.070383+00:00
-- url     : https://prove2.me/submissions/ec4ed265-153a-4779-9b33-fbcfdb61bc99

import Definitions.Def_CollatzEndpointTransport_Common_TerrasAffineIterate
import Definitions.Def_CollatzEndpointTransport_Common_TerrasIntegerAffine
import Theorems.Thm_CollatzEndpointTransport_Terras_integerCorrection_zero
import Theorems.Thm_CollatzEndpointTransport_Terras_oddCount_succ

attribute [local simp] CollatzEndpointTransport.Terras.integerCorrection_zero

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset
namespace CollatzEndpointTransport.Terras
theorem _root_.solution
    {M n j : ℕ} (hjM : j ≤ M) (hn : n < 2 ^ M) :
    (T^[j]) n < 3 ^ oddCount j n * 2 ^ (M - j) := by
  induction j generalizing M n with
  | zero =>
      simpa [oddCount] using hn
  | succ j ih =>
      have hjM' : j ≤ M := by omega
      have hprev := ih hjM' hn
      have hsub : M - j = (M - (j + 1)) + 1 := by omega
      rw [hsub, pow_succ] at hprev
      rw [Function.iterate_succ_apply', oddCount_succ]
      by_cases hp : parityBit ((T^[j]) n) = true
      · have hmod : (T^[j]) n % 2 = 1 := by
          simpa [parityBit, decide_eq_true_eq] using hp
        have hstep := two_mul_T_of_odd hmod
        rw [hp]
        simp only [if_true, pow_succ]
        nlinarith
      · have hpFalse : parityBit ((T^[j]) n) = false := by
          cases h : parityBit ((T^[j]) n) <;> simp_all
        have hmod : (T^[j]) n % 2 = 0 := by
          simp only [parityBit, hpFalse, decide_eq_false_iff_not] at hpFalse
          omega
        have hstep := two_mul_T_of_even hmod
        rw [hpFalse]
        simp only [Bool.false_eq_true, if_false, Nat.add_zero]
        nlinarith
end CollatzEndpointTransport.Terras
