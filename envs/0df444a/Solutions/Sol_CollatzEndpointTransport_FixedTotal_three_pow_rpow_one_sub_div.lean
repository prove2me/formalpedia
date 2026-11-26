-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.three_pow_rpow_one_sub_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:06:26.007159+00:00
-- url     : https://prove2.me/submissions/2b74f679-5ce3-4edc-9c3e-75ccd983ad5b

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalLevelBadMass
import Definitions.Def_CollatzEndpointTransport_Linear_OptimizedLinearPullbackConstants
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalNonlinearShell

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    (D : ℝ) (n : ℕ) :
    ((3 : ℝ) ^ n) ^ (1 - D) / (3 : ℝ) ^ n =
      (Real.exp (-D * Real.log 3)) ^ n := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hpow : 0 < (3 : ℝ) ^ n := pow_pos h3 _
  have hpowexp :
      (3 : ℝ) ^ n =
        Real.exp ((n : ℝ) * Real.log 3) := by
    calc
      (3 : ℝ) ^ n =
          (Real.exp (Real.log 3)) ^ n := by
            rw [Real.exp_log h3]
      _ = Real.exp ((n : ℝ) * Real.log 3) := by
            rw [← Real.exp_nat_mul]
  rw [hpowexp]
  rw [Real.rpow_def_of_pos (Real.exp_pos _)]
  rw [Real.log_exp]
  rw [← Real.exp_sub]
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  ring
end CollatzEndpointTransport.FixedTotal
