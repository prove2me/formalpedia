-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.centralSourceEndpointBad_div_pow_le_balanced_sharp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:57:24.725378+00:00
-- url     : https://prove2.me/submissions/aeef37fc-6379-4c0a-877c-2f8fcdb27fa3

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiPullback
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Definitions.Def_CollatzEndpointTransport_Linear_SharpCentralRenyiPullback
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralEndpointInformation_le_sharp
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiThreshold_mul_oddRate
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiThreshold_neg_rpow
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiThreshold_pos
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralSourceEndpointBad_div_pow_le


set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {S : Set ℕ} {C D theta eta : ℝ}
    (hS : QuantitativeDensity.IsCDDense S C D)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2)
    (M : ℕ) :
    ((centralSourceEndpointBad S M theta eta).card : ℝ) /
        (2 ^ M : ℝ) ≤
      (C * Real.exp (-D * Real.log 3) +
          2 * (3 : ℝ) ^ theta * centralMomentConstant theta eta *
            (M + 1 : ℝ) ^ (1 + theta)) *
        Real.exp (-centralRenyiRate theta D * M) := by
  have hbase := centralSourceEndpointBad_div_pow_le hS M theta eta
    (centralRenyiThreshold theta D M)
    (centralRenyiThreshold_pos theta D M) htheta0
  have hmoment := centralEndpointInformation_le_sharp
    htheta0 htheta1 heta0 heta1 (M := M)
  calc
    ((centralSourceEndpointBad S M theta eta).card : ℝ) / (2 ^ M : ℝ) ≤
      C * centralRenyiThreshold theta D M * Real.exp (-D * Real.log 3) *
          ((1 + Real.exp (-D * Real.log 3)) / 2) ^ M +
        (centralRenyiThreshold theta D M) ^ (-theta) *
          centralEndpointInformation M theta eta := hbase
    _ ≤ C * centralRenyiThreshold theta D M * Real.exp (-D * Real.log 3) *
          ((1 + Real.exp (-D * Real.log 3)) / 2) ^ M +
        (centralRenyiThreshold theta D M) ^ (-theta) *
          (2 * (3 : ℝ) ^ theta * centralMomentConstant theta eta *
            (M + 1 : ℝ) ^ (1 + theta)) := by
      apply add_le_add_right
      exact mul_le_mul_of_nonneg_left hmoment
        (Real.rpow_nonneg (centralRenyiThreshold_pos theta D M).le _)
    _ = (C * Real.exp (-D * Real.log 3) +
          2 * (3 : ℝ) ^ theta * centralMomentConstant theta eta *
            (M + 1 : ℝ) ^ (1 + theta)) *
        Real.exp (-centralRenyiRate theta D * M) := by
      rw [centralRenyiThreshold_neg_rpow M htheta0]
      rw [show
        C * centralRenyiThreshold theta D M * Real.exp (-D * Real.log 3) *
            ((1 + Real.exp (-D * Real.log 3)) / 2) ^ M =
          C * Real.exp (-D * Real.log 3) *
            (centralRenyiThreshold theta D M *
              ((1 + Real.exp (-D * Real.log 3)) / 2) ^ M) by ring]
      rw [centralRenyiThreshold_mul_oddRate M htheta0]
      ring
end CollatzEndpointTransport.FixedTotal
