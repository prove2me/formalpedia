-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.targetBinomialFactor_rpow_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:51:10.168697+00:00
-- url     : https://prove2.me/submissions/b3022b74-208b-404e-a715-57df8efb1523

import Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralRenyiShellTransport
import Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralEndpointInformation
import Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralRenyiMomentTransport
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_oddCountRate_pow_eq_exp


set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {C D theta : ℝ} (M : ℕ)
    (hC : 0 < C) (htheta : 0 < theta) :
    (C * Real.exp (-D * Real.log 3) *
        ((1 + Real.exp (-D * Real.log 3)) / 2) ^ M) ^
          (theta / (1 + theta)) =
      (C * Real.exp (-D * Real.log 3)) ^ (theta / (1 + theta)) *
        Real.exp (-centralRenyiRate theta D * M) := by
  have hq : 0 < 1 + theta := by linarith
  have hfront : 0 ≤ C * Real.exp (-D * Real.log 3) := by positivity
  rw [oddCountRate_pow_eq_exp]
  rw [Real.mul_rpow hfront (Real.exp_nonneg _)]
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  congr 1
  unfold centralRenyiRate
  field_simp [hq.ne']
end CollatzEndpointTransport.FixedTotal
