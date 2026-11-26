-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.centralRenyi_lateDiscardRatio_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:38:21.646285+00:00
-- url     : https://prove2.me/submissions/151aa886-d543-4c56-99a7-65b6999f25c8

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiShell
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalNonlinearShell
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiPullback

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real Topology
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.centralPullbackSourceCodeDecidableEq
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {M K : ℕ} (hKM : K ≤ M) :
    ((((M + 1) * 2 ^ (M - K) : ℕ) : ℝ) / (2 ^ M : ℝ)) =
      (M + 1 : ℝ) * Real.exp (-(Real.log 2) * K) := by
  push_cast
  rw [pow_sub₀ (2 : ℝ) (by norm_num) hKM]
  have hpow : (2 : ℝ) ^ K = Real.exp (Real.log 2 * K) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
  rw [hpow, show -Real.log 2 * (K : ℝ) =
      -(Real.log 2 * K) by ring, Real.exp_neg]
  field_simp
end CollatzEndpointTransport.FixedTotal
