-- Prove2me | solution 1 for CollatzEndpointTransport.Terras.T_cast_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:13:45.319311+00:00
-- url     : https://prove2.me/submissions/acdd68d0-8ed5-4d4b-b886-c1f576d51de1

import Definitions.Def_CollatzEndpointTransport_Common_AffineCorrection
import Definitions.Def_CollatzEndpointTransport_Common_TerrasAffineIterate

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset
namespace CollatzEndpointTransport.Terras
theorem _root_.solution (x : ℕ) :
    (T x : ℝ) =
      ((3 : ℝ) ^ (if parityBit x then 1 else 0) * x +
        (if parityBit x then 1 else 0)) / 2 := by
  rcases Nat.even_or_odd x with he | ho
  · have hx : x % 2 = 0 := Nat.even_iff.mp he
    have hp : parityBit x = false := by
      simp [parityBit, hx]
    rw [hp]
    norm_num
    have hT := two_mul_T_of_even hx
    have hTR : (2 : ℝ) * T x = x := by exact_mod_cast hT
    linarith
  · have hx : x % 2 = 1 := Nat.odd_iff.mp ho
    have hp : parityBit x = true := by
      simp [parityBit, hx]
    rw [hp]
    norm_num
    have hT := two_mul_T_of_odd hx
    have hTR : (2 : ℝ) * T x = 3 * x + 1 := by exact_mod_cast hT
    linarith
end CollatzEndpointTransport.Terras
