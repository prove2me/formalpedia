-- Prove2me | solution 1 for CollatzEndpointTransport.QuantitativeDensity.lg3_lt_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:15:46.898867+00:00
-- url     : https://prove2.me/submissions/b8d3184e-6e80-442c-9641-44422179eb2c

import Mathlib
import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensityConstants

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.QuantitativeDensity
namespace CollatzEndpointTransport.QuantitativeDensity
theorem _root_.solution : lg3 < 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h34 : Real.log 3 < Real.log 4 :=
    Real.log_lt_log (by norm_num) (by norm_num)
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    push_cast
    ring
  unfold lg3 Real.logb
  rw [div_lt_iff₀ hlog2]
  linarith
end CollatzEndpointTransport.QuantitativeDensity
