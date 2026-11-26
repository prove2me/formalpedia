-- Prove2me | solution 1 for CollatzEndpointTransport.Terras.integerCorrection_lt_scale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:24:21.168863+00:00
-- url     : https://prove2.me/submissions/69a663de-81fc-4072-9b8b-bc0fd61feac8

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
    integerCorrection k n <
      3 ^ oddCount k n * 2 ^ k := by
  induction k with
  | zero =>
      simp [integerCorrection, oddCount]
  | succ k ih =>
      rw [integerCorrection_succ, oddCount_succ]
      by_cases hp : parityBit ((T^[k]) n) = true
      · rw [hp]
        simp only [if_true, pow_succ]
        have hpow : 0 < 2 ^ k := pow_pos (by norm_num) _
        have hthree : 1 ≤ 3 ^ oddCount k n :=
          one_le_pow₀ (by norm_num)
        nlinarith
      · have hpFalse : parityBit ((T^[k]) n) = false := by
          cases h : parityBit ((T^[k]) n) <;> simp_all
        rw [hpFalse]
        simp only [Bool.false_eq_true, if_false, pow_succ]
        have hscale : 0 < 3 ^ oddCount k n * 2 ^ k := by positivity
        calc
          integerCorrection k n <
              3 ^ oddCount k n * 2 ^ k := ih
          _ < (3 ^ oddCount k n * 2 ^ k) * 2 :=
            lt_mul_of_one_lt_right hscale (by norm_num)
          _ = 3 ^ (oddCount k n + 0) * (2 ^ k * 2) := by
            simp
            ring
end CollatzEndpointTransport.Terras
