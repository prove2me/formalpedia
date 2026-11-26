-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.centralRenyiShellRate_lt_log_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:18:21.730595+00:00
-- url     : https://prove2.me/submissions/c26527e4-3882-4a97-b760-bef2afe195f6

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiShell
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalNonlinearShell
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiPullback
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiAbsorption_lt_one
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiRate_pos
import Theorems.Thm_CollatzEndpointTransport_OptimizedLinearPullback_psi_inner_pos
import Theorems.Thm_CollatzEndpointTransport_OptimizedLinearPullback_psi_pos


set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real Topology
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.centralPullbackSourceCodeDecidableEq
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {theta transport D : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (htransport0 : 0 < transport)
    (htransport : transport < centralRenyiAsymptoticRate theta)
    (hD : 0 < D) :
    centralRenyiShellRate theta transport D < Real.log 2 := by
  have hz1 := centralRenyiAbsorption_lt_one htheta0 htransport
  have hr0 := centralRenyiRate_pos htheta0 hD
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hinner := OptimizedLinearPullback.psi_inner_pos D
  have hlt :
      (1 / 2 : ℝ) <
        (1 + Real.exp (-D * Real.log 3)) / 2 := by
    have := Real.exp_pos (-D * Real.log 3)
    linarith
  have hlog := Real.strictMonoOn_log hhalf hinner hlt
  have hlogHalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
      Real.log_inv]
  have hpsi : OptimizedLinearPullback.psi D < Real.log 2 := by
    unfold OptimizedLinearPullback.psi
    rw [hlogHalf] at hlog
    linarith
  have hthetaFrac : theta / (1 + theta) < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  have hratePsi :
      centralRenyiRate theta D < OptimizedLinearPullback.psi D := by
    unfold centralRenyiRate
    exact mul_lt_of_lt_one_left
      (OptimizedLinearPullback.psi_pos hD) hthetaFrac
  unfold centralRenyiShellRate
  exact (mul_lt_of_lt_one_left hr0 hz1).trans
    (hratePsi.trans hpsi)
end CollatzEndpointTransport.FixedTotal
