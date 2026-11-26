-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.centralSourceEndpointBad_div_pow_le_holder_moment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:03:10.529251+00:00
-- url     : https://prove2.me/submissions/fb1a9b74-31a4-4486-ac0f-47de7e5265f3

import Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralRenyiShellTransport
import Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralEndpointInformation
import Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralRenyiMomentTransport
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralEndpointInformation_rpow_le_holder
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_targetBinomialFactor_rpow_eq
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralSourceEndpointBad_div_pow_le_holder
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_IsCDDense_C_pos


set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
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
    ((centralSourceEndpointBad S M theta eta).card : ℝ) / (2 : ℝ) ^ M ≤
      (C * Real.exp (-D * Real.log 3)) ^
          (theta / (1 + theta)) *
        holderCentralMomentConstant theta eta *
        (M + 1 : ℝ) ^ (theta / (2 * (1 + theta))) *
        Real.exp (-centralRenyiRate theta D * M) := by
  have hbase := centralSourceEndpointBad_div_pow_le_holder
    hS M theta eta htheta0
  have hmoment := centralEndpointInformation_rpow_le_holder
    htheta0 htheta1 heta0 heta1 (M := M)
  have htarget0 : 0 ≤
      (C * Real.exp (-D * Real.log 3) *
        ((1 + Real.exp (-D * Real.log 3)) / 2) ^ M) ^
          (theta / (1 + theta)) := by
    apply Real.rpow_nonneg
    exact mul_nonneg
      (mul_nonneg hS.C_pos.le (Real.exp_nonneg _))
      (pow_nonneg (by positivity) _)
  calc
    ((centralSourceEndpointBad S M theta eta).card : ℝ) / (2 : ℝ) ^ M ≤
        (C * Real.exp (-D * Real.log 3) *
          ((1 + Real.exp (-D * Real.log 3)) / 2) ^ M) ^
            (theta / (1 + theta)) *
          (centralEndpointInformation M theta eta) ^
            (1 / (1 + theta)) := hbase
    _ ≤ (C * Real.exp (-D * Real.log 3) *
          ((1 + Real.exp (-D * Real.log 3)) / 2) ^ M) ^
            (theta / (1 + theta)) *
          (holderCentralMomentConstant theta eta *
            (M + 1 : ℝ) ^ (theta / (2 * (1 + theta)))) :=
      mul_le_mul_of_nonneg_left hmoment htarget0
    _ = (C * Real.exp (-D * Real.log 3)) ^
            (theta / (1 + theta)) *
          holderCentralMomentConstant theta eta *
          (M + 1 : ℝ) ^ (theta / (2 * (1 + theta))) *
          Real.exp (-centralRenyiRate theta D * M) := by
      rw [targetBinomialFactor_rpow_eq M hS.C_pos htheta0]
      ring
end CollatzEndpointTransport.FixedTotal
