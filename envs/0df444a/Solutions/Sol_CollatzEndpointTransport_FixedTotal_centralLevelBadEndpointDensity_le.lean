-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.centralLevelBadEndpointDensity_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:49:55.16786+00:00
-- url     : https://prove2.me/submissions/52877809-974a-4950-9146-96114a87172f

import Definitions.Def_CollatzEndpointTransport_Linear_SharpCentralRenyiPullback
import Mathlib.Analysis.MeanInequalities
import Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralRenyiTransport
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_centralLevelBadEndpointSet_le
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_three_pow_rpow_one_sub_div


set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {S : Set ℕ} {C D : ℝ}
    (hS : QuantitativeDensity.IsCDDense S C D)
    (M s : ℕ) (theta eta : ℝ) :
    ((centralLevelBadEndpointSet S M s theta eta).card : ℝ) /
        (3 : ℝ) ^ (s + 1) ≤
      C * (Real.exp (-D * Real.log 3)) ^ (s + 1) := by
  have hcard := card_centralLevelBadEndpointSet_le hS M s theta eta
  have hpow : 0 < (3 : ℝ) ^ (s + 1) := by positivity
  calc
    ((centralLevelBadEndpointSet S M s theta eta).card : ℝ) /
          (3 : ℝ) ^ (s + 1) ≤
        (C * ((3 : ℝ) ^ (s + 1)) ^ (1 - D)) /
          (3 : ℝ) ^ (s + 1) :=
      div_le_div_of_nonneg_right hcard hpow.le
    _ = C * ((((3 : ℝ) ^ (s + 1)) ^ (1 - D)) /
          (3 : ℝ) ^ (s + 1)) := by ring
    _ = C * (Real.exp (-D * Real.log 3)) ^ (s + 1) := by
      rw [three_pow_rpow_one_sub_div]
end CollatzEndpointTransport.FixedTotal
