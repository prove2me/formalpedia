-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.annular_fractional_decay_le_geometric
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:46:10.998376+00:00
-- url     : https://prove2.me/submissions/78b84a59-8588-44a9-a138-7587a35eee73

import Definitions.Def_CollatzEndpointTransport_Linear_FractionalBinomialMass
import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_CollatzEndpointTransport_Linear_FractionalBinomialMassBound

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
set_option maxHeartbeats 400000
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {j : ℕ} {theta : ℝ} (htheta0 : 0 < theta) (htheta1 : theta < 1) :
    (2 * Real.exp (-2 * (j : ℝ) ^ 2)) ^ (1 - theta) ≤
      (2 : ℝ) ^ (1 - theta) *
        (Real.exp (-2 * (1 - theta))) ^ j := by
  rw [Real.mul_rpow (by norm_num) (Real.exp_nonneg _)]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by norm_num) _)
  rw [← Real.exp_mul]
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have hjNat : j ≤ j * j := Nat.le_mul_self j
  have hj : (j : ℝ) ≤ (j : ℝ) ^ 2 := by
    exact_mod_cast (by simpa [pow_two] using hjNat)
  nlinarith
end CollatzEndpointTransport.FixedTotal
