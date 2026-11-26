-- Prove2me | solution 1 for CollatzEndpointTransport.Terras.three_rpow_eq_two_rpow_lg3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:19:19.849204+00:00
-- url     : https://prove2.me/submissions/4143d507-e89d-4c94-b925-fbb42c4c1352

import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensityConstants
import Definitions.Def_CollatzEndpointTransport_Common_TerrasAffineIterate
import Definitions.Def_CollatzEndpointTransport_Common_TerrasOrbitEnvelope

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset
open scoped Real
namespace CollatzEndpointTransport.Terras
theorem _root_.solution (x : ℝ) :
    (3 : ℝ) ^ x =
      (2 : ℝ) ^ (QuantitativeDensity.lg3 * x) := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3),
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  congr 1
  have hlog2 : Real.log 2 ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num))
  unfold QuantitativeDensity.lg3 Real.logb
  field_simp
end CollatzEndpointTransport.Terras
