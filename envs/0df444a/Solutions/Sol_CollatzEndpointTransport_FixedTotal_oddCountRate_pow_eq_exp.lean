-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.oddCountRate_pow_eq_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:07:34.212688+00:00
-- url     : https://prove2.me/submissions/3fa3dd0a-bb20-485b-bbab-4b41cebb1bc7

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalLevelBadMass
import Definitions.Def_CollatzEndpointTransport_Linear_OptimizedLinearPullbackConstants
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalNonlinearShell
import Theorems.Thm_CollatzEndpointTransport_OptimizedLinearPullback_psi_inner_pos


set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    (D : ℝ) (M : ℕ) :
    ((1 + Real.exp (-D * Real.log 3)) / 2) ^ M =
      Real.exp (-OptimizedLinearPullback.psi D * M) := by
  have hinner :=
    OptimizedLinearPullback.psi_inner_pos D
  calc
    ((1 + Real.exp (-D * Real.log 3)) / 2) ^ M =
        (Real.exp
          (Real.log ((1 + Real.exp (-D * Real.log 3)) / 2))) ^ M := by
      rw [Real.exp_log hinner]
    _ = Real.exp
        ((M : ℝ) *
          Real.log ((1 + Real.exp (-D * Real.log 3)) / 2)) := by
      rw [← Real.exp_nat_mul]
    _ = Real.exp (-OptimizedLinearPullback.psi D * M) := by
      congr 1
      unfold OptimizedLinearPullback.psi
      push_cast
      ring
end CollatzEndpointTransport.FixedTotal
