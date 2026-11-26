-- Prove2me | solution 1 for CollatzEndpointTransport.Terras.centralOrbitScale_eq_two_rpow_neg_b
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:20:58.964855+00:00
-- url     : https://prove2.me/submissions/3e9b3fd7-b915-4cf9-aaaa-652b9248709a

import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensityConstants
import Definitions.Def_CollatzEndpointTransport_Common_TerrasAffineIterate
import Definitions.Def_CollatzEndpointTransport_Common_TerrasOrbitEnvelope
import Theorems.Thm_CollatzEndpointTransport_Terras_three_rpow_eq_two_rpow_lg3

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset
open scoped Real
namespace CollatzEndpointTransport.Terras
theorem _root_.solution (k : ℕ) :
    centralOrbitScale k =
      (2 : ℝ) ^ (-QuantitativeDensity.bConst * k) := by
  unfold centralOrbitScale
  rw [three_rpow_eq_two_rpow_lg3, ← Real.rpow_natCast,
    ← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
  congr 1
  unfold QuantitativeDensity.bConst QuantitativeDensity.a0
  ring
end CollatzEndpointTransport.Terras
