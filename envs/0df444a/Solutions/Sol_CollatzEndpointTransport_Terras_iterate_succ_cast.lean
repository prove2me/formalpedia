-- Prove2me | solution 1 for CollatzEndpointTransport.Terras.iterate_succ_cast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:19:11.546269+00:00
-- url     : https://prove2.me/submissions/63e3aa58-a931-4979-80eb-172a21527a5a

import Definitions.Def_CollatzEndpointTransport_Common_AffineCorrection
import Definitions.Def_CollatzEndpointTransport_Common_TerrasAffineIterate
import Theorems.Thm_CollatzEndpointTransport_Terras_T_cast_step

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset
namespace CollatzEndpointTransport.Terras
theorem _root_.solution (k n : ℕ) :
    ((T^[k + 1]) n : ℝ) =
      ((3 : ℝ) ^ (if parityBit ((T^[k]) n) then 1 else 0) *
          ((T^[k]) n : ℝ) +
        parityDigitR n k) / 2 := by
  rw [Function.iterate_succ_apply']
  rw [T_cast_step]
  rfl
end CollatzEndpointTransport.Terras
