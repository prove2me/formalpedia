-- Prove2me | solution 1 for CollatzEndpointTransport.Terras.pow_two_mul_iterate_eq_affine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:21:38.659902+00:00
-- url     : https://prove2.me/submissions/067b3880-0181-4efe-a1e0-ae9690f5dd1d

import Definitions.Def_CollatzEndpointTransport_Common_TerrasAffineIterate
import Definitions.Def_CollatzEndpointTransport_Common_TerrasIntegerAffine
import Theorems.Thm_CollatzEndpointTransport_Terras_integerCorrection_zero
import Theorems.Thm_CollatzEndpointTransport_Terras_integerCorrection_succ
import Theorems.Thm_CollatzEndpointTransport_Terras_oddCount_succ

attribute [local simp] CollatzEndpointTransport.Terras.integerCorrection_zero

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset
namespace CollatzEndpointTransport.Terras
theorem _root_.solution (k n : ℕ) :
    2 ^ k * (T^[k]) n =
      3 ^ oddCount k n * n + integerCorrection k n := by
  induction k with
  | zero =>
      simp [integerCorrection, oddCount]
  | succ k ih =>
      rw [integerCorrection_succ, oddCount_succ]
      by_cases hp : parityBit ((T^[k]) n) = true
      · have hmod : (T^[k]) n % 2 = 1 := by
          simpa [parityBit, decide_eq_true_eq] using hp
        have hstep := two_mul_T_of_odd hmod
        rw [Function.iterate_succ_apply', hp]
        simp only [if_true, pow_succ]
        calc
          2 ^ (k + 1) * T ((T^[k]) n)
              = 2 ^ k * (2 * T ((T^[k]) n)) := by ring
          _ = 2 ^ k * (3 * (T^[k]) n + 1) := by rw [hstep]
          _ = 3 * (2 ^ k * (T^[k]) n) + 2 ^ k := by ring
          _ = 3 * (3 ^ oddCount k n * n + integerCorrection k n) +
                2 ^ k := by rw [ih]
          _ = 3 ^ (oddCount k n + 1) * n +
                (3 * integerCorrection k n + 2 ^ k) := by
            rw [pow_succ]
            ring
      · have hpFalse : parityBit ((T^[k]) n) = false := by
          cases h : parityBit ((T^[k]) n) <;> simp_all
        have hmod : (T^[k]) n % 2 = 0 := by
          simp only [parityBit, hpFalse, decide_eq_false_iff_not] at hpFalse
          omega
        have hstep := two_mul_T_of_even hmod
        rw [Function.iterate_succ_apply', hpFalse]
        calc
          2 ^ (k + 1) * T ((T^[k]) n)
              = 2 ^ k * (2 * T ((T^[k]) n)) := by ring
          _ = 2 ^ k * (T^[k]) n := by rw [hstep]
          _ = 3 ^ oddCount k n * n + integerCorrection k n := ih
end CollatzEndpointTransport.Terras
