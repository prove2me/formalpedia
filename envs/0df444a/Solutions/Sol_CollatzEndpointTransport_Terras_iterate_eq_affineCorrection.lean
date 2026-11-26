-- Prove2me | solution 1 for CollatzEndpointTransport.Terras.iterate_eq_affineCorrection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:20:43.281191+00:00
-- url     : https://prove2.me/submissions/4e8e9702-ed60-4f75-a81f-9540ceaee47d

import Definitions.Def_CollatzEndpointTransport_Common_AffineCorrection
import Definitions.Def_CollatzEndpointTransport_Common_TerrasAffineIterate
import Theorems.Thm_CollatzEndpointTransport_Terras_oddCount_succ
import Theorems.Thm_CollatzEndpointTransport_Terras_affineCorrection_succ
import Theorems.Thm_CollatzEndpointTransport_Terras_iterate_succ_cast

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset
namespace CollatzEndpointTransport.Terras
theorem _root_.solution (k n : ℕ) :
    ((T^[k]) n : ℝ) =
      ((n : ℝ) / (2 : ℝ) ^ k + affineCorrection k n) *
        (3 : ℝ) ^ oddCount k n := by
  induction k with
  | zero =>
      simp [affineCorrection, oddCount]
  | succ k ih =>
      rw [iterate_succ_cast, affineCorrection_succ, oddCount_succ, ih]
      by_cases hp : parityBit ((T^[k]) n) = true
      · simp [hp, parityDigitR, pow_succ]
        field_simp
        ring
      · have hpFalse : parityBit ((T^[k]) n) = false := by
          cases h : parityBit ((T^[k]) n) <;> simp_all
        simp [hpFalse, parityDigitR, pow_succ]
        ring
end CollatzEndpointTransport.Terras
