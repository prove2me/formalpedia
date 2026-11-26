-- Prove2me | solution 1 for CollatzEndpointTransport.Terras.one_add_exp_neg_four_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:23:29.440798+00:00
-- url     : https://prove2.me/submissions/56c7b1f1-5163-4a1d-ae7a-5374249f021a

import Definitions.Def_CollatzEndpointTransport_Common_TerrasParityBijection
import Definitions.Def_CollatzEndpointTransport_Common_TerrasBinomialTail

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset
namespace CollatzEndpointTransport.Terras
theorem _root_.solution (t : ℝ) :
    1 + Real.exp (-4 * t) ≤ 2 * Real.exp (-2 * t + 2 * t ^ 2) := by
  have hcosh := Real.cosh_le_exp_half_sq (2 * t)
  have hmul :
      2 * Real.exp (-2 * t) * Real.cosh (2 * t) ≤
        2 * Real.exp (-2 * t) * Real.exp ((2 * t) ^ 2 / 2) :=
    mul_le_mul_of_nonneg_left hcosh (by positivity)
  calc
    1 + Real.exp (-4 * t) =
        2 * Real.exp (-2 * t) * Real.cosh (2 * t) := by
      rw [Real.cosh_eq]
      have hcancel :
          Real.exp (-2 * t) * Real.exp (2 * t) = 1 := by
        rw [← Real.exp_add]
        rw [show -2 * t + 2 * t = 0 by ring, Real.exp_zero]
      have hdouble :
          Real.exp (-2 * t) * Real.exp (-(2 * t)) =
            Real.exp (-4 * t) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [show 2 * Real.exp (-2 * t) *
            ((Real.exp (2 * t) + Real.exp (-(2 * t))) / 2) =
          Real.exp (-2 * t) * Real.exp (2 * t) +
            Real.exp (-2 * t) * Real.exp (-(2 * t)) by ring]
      rw [hcancel, hdouble]
    _ ≤ 2 * Real.exp (-2 * t) * Real.exp ((2 * t) ^ 2 / 2) := hmul
    _ = 2 * Real.exp (-2 * t + 2 * t ^ 2) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
end CollatzEndpointTransport.Terras
