-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.centralRenyiThreshold_mul_oddRate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:17:27.245023+00:00
-- url     : https://prove2.me/submissions/3b588df6-bdb0-4cd4-af0b-658c788ae709

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiShell
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalNonlinearShell
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiPullback
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_oddCountRate_pow_eq_exp


set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real Topology
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.centralPullbackSourceCodeDecidableEq
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {theta D : ℝ} (M : ℕ) (htheta : 0 < theta) :
    centralRenyiThreshold theta D M *
        ((1 + Real.exp (-D * Real.log 3)) / 2) ^ M =
      Real.exp (-centralRenyiRate theta D * M) := by
  rw [oddCountRate_pow_eq_exp]
  unfold centralRenyiThreshold centralRenyiRate
  rw [← Real.exp_add]
  congr 1
  have hden : 0 < 1 + theta := by linarith
  field_simp [hden.ne']
  ring
end CollatzEndpointTransport.FixedTotal
