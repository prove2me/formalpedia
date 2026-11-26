-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.holder_product_normalization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:50:14.489929+00:00
-- url     : https://prove2.me/submissions/c4d76bf6-cb9b-48c3-b629-067beb4a771f

import Definitions.Def_CollatzEndpointTransport_Linear_SharpCentralRenyiPullback
import Mathlib.Analysis.MeanInequalities
import Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralRenyiTransport

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {E moment info N R P theta : ℝ}
    (hN : 0 < N) (hR : 0 < R) (hP : 0 < P)
    (hE : 0 ≤ E) (hmoment : 0 ≤ moment)
    (hinfo : info = (R / N) ^ theta * moment)
    (htheta : 0 < theta) :
    E ^ (theta / (1 + theta)) *
          moment ^ (1 / (1 + theta)) / P =
      (N / P) * (E / R) ^ (theta / (1 + theta)) *
        (info / N) ^ (1 / (1 + theta)) := by
  have hq : 0 < 1 + theta := by linarith
  have hRN : 0 ≤ R / N := (div_pos hR hN).le
  have hinfo0 : 0 ≤ info := by rw [hinfo]; positivity
  rw [hinfo]
  rw [Real.div_rpow hE hR.le]
  rw [Real.div_rpow (mul_nonneg (Real.rpow_nonneg hRN _) hmoment) hN.le]
  rw [Real.mul_rpow (Real.rpow_nonneg hRN _) hmoment]
  rw [← Real.rpow_mul hRN]
  have hmul : theta * (1 / (1 + theta)) = theta / (1 + theta) := by ring
  rw [hmul]
  rw [Real.div_rpow hR.le hN.le]
  field_simp [hN.ne', hR.ne', hP.ne']
  have hsum :
      theta / (1 + theta) + 1 / (1 + theta) = 1 := by
    field_simp [hq.ne']
    ring
  have hNpow :
      N ^ (theta / (1 + theta)) * N ^ (1 / (1 + theta)) = N := by
    rw [← Real.rpow_add hN, hsum, Real.rpow_one]
  rw [show
    E ^ (theta / (1 + theta)) * moment ^ (1 / (1 + theta)) *
          N ^ (theta / (1 + theta)) * N ^ (1 / (1 + theta)) =
        (E ^ (theta / (1 + theta)) * moment ^ (1 / (1 + theta))) *
          (N ^ (theta / (1 + theta)) * N ^ (1 / (1 + theta))) by ring]
  rw [hNpow]
end CollatzEndpointTransport.FixedTotal
