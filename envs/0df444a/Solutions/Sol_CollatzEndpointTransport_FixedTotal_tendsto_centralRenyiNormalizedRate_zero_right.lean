-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.tendsto_centralRenyiNormalizedRate_zero_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:36:46.825799+00:00
-- url     : https://prove2.me/submissions/febae3ee-18ea-4d11-b345-4878d71e4c10

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiShell
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalNonlinearShell
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiPullback
import Theorems.Thm_CollatzEndpointTransport_OptimizedLinearPullback_tendsto_psi_div_zero_right


set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real Topology
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.centralPullbackSourceCodeDecidableEq
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution (theta : ℝ) :
    Filter.Tendsto (centralRenyiNormalizedRate theta)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (centralRenyiAsymptoticRate theta)) := by
  have h :=
    (OptimizedLinearPullback.tendsto_psi_div_zero_right.const_mul
      (theta / (1 + theta))).div_const (Real.log 2)
  convert h using 1
  · funext D
    unfold centralRenyiNormalizedRate centralRenyiRate
    ring
  · unfold centralRenyiAsymptoticRate
    ring
end CollatzEndpointTransport.FixedTotal
