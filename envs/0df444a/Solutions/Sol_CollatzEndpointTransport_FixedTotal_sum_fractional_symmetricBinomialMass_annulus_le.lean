-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.sum_fractional_symmetricBinomialMass_annulus_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:48:20.609611+00:00
-- url     : https://prove2.me/submissions/a78e109b-8961-4d14-a688-b87af28a5314

import Definitions.Def_CollatzEndpointTransport_Linear_FractionalBinomialMass
import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_CollatzEndpointTransport_Linear_FractionalBinomialMassBound
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_rpow_one_sub_le_card_rpow_mul_sum_rpow
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_binomialAnnulus_card_rpow_le
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_symmetricBinomialMass_annulus_le


set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
set_option maxHeartbeats 400000
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {H j : ℕ} {theta : ℝ}
    (hH : 0 < H) (htheta0 : 0 < theta) (htheta1 : theta < 1) :
    (∑ k ∈ binomialAnnulus H j,
        (symmetricBinomialMass H k) ^ (1 - theta)) ≤
      ((8 : ℝ) ^ theta * (H + 1 : ℝ) ^ (theta / 2)) *
        (2 * Real.exp (-2 * (j : ℝ) ^ 2)) ^ (1 - theta) := by
  have hconc := sum_rpow_one_sub_le_card_rpow_mul_sum_rpow
    (binomialAnnulus H j) (symmetricBinomialMass H)
    htheta0 htheta1
    (fun k hk => by unfold symmetricBinomialMass; positivity)
  have hcard := binomialAnnulus_card_rpow_le
    (H := H) (j := j) htheta0
  have hmass := sum_symmetricBinomialMass_annulus_le
    (H := H) (j := j) hH
  have hmassPow :
      (∑ k ∈ binomialAnnulus H j, symmetricBinomialMass H k) ^
          (1 - theta) ≤
        (2 * Real.exp (-2 * (j : ℝ) ^ 2)) ^ (1 - theta) := by
    exact Real.rpow_le_rpow
      (Finset.sum_nonneg fun k hk => by unfold symmetricBinomialMass; positivity)
      hmass (by linarith)
  calc
    (∑ k ∈ binomialAnnulus H j,
        (symmetricBinomialMass H k) ^ (1 - theta)) ≤
        ((binomialAnnulus H j).card : ℝ) ^ theta *
          (∑ k ∈ binomialAnnulus H j, symmetricBinomialMass H k) ^
            (1 - theta) := hconc
    _ ≤ ((8 : ℝ) ^ theta * (H + 1 : ℝ) ^ (theta / 2)) *
          (2 * Real.exp (-2 * (j : ℝ) ^ 2)) ^ (1 - theta) := by
      exact mul_le_mul hcard hmassPow
        (Real.rpow_nonneg (Finset.sum_nonneg fun k hk => by
          unfold symmetricBinomialMass
          positivity) _)
        (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
          (Real.rpow_nonneg (by positivity) _))
end CollatzEndpointTransport.FixedTotal
