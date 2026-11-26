-- Prove2me | solution 1 for CollatzEndpointTransport.Terras.centralOrbitScale_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:55:47.487558+00:00
-- url     : https://prove2.me/submissions/1f3fc550-38c4-4d1d-a72a-69c71512d8da

import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensityConstants
import Definitions.Def_CollatzEndpointTransport_Common_TerrasAffineIterate
import Definitions.Def_CollatzEndpointTransport_Common_TerrasOrbitEnvelope

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset
open scoped Real
namespace CollatzEndpointTransport.Terras
theorem _root_.solution (k : ℕ) :
    centralOrbitScale k = (Real.sqrt 3 / 2) ^ k := by
  unfold centralOrbitScale
  rw [Real.rpow_div_two_eq_sqrt (k : ℝ) (by norm_num),
    Real.rpow_natCast, div_pow]
end CollatzEndpointTransport.Terras
