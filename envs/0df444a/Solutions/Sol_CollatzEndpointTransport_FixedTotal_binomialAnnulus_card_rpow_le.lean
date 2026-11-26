-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.binomialAnnulus_card_rpow_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:46:08.942324+00:00
-- url     : https://prove2.me/submissions/174d4079-cef0-4ad5-93c9-5dd3afe79de2

import Definitions.Def_CollatzEndpointTransport_Linear_FractionalBinomialMass
import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_CollatzEndpointTransport_Linear_FractionalBinomialMassBound
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_binomialAnnulus_card_le


set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
set_option maxHeartbeats 400000
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {H j : ℕ} {theta : ℝ} (htheta0 : 0 < theta) :
    ((binomialAnnulus H j).card : ℝ) ^ theta ≤
      (8 : ℝ) ^ theta * (H + 1 : ℝ) ^ (theta / 2) := by
  have hcardNat := binomialAnnulus_card_le H j
  have hcard : ((binomialAnnulus H j).card : ℝ) ≤
      2 * (binomialAnnulusWidth H : ℝ) := by exact_mod_cast hcardNat
  have hsqrtNat : (Nat.sqrt H : ℝ) ≤ Real.sqrt H :=
    Real.nat_sqrt_le_real_sqrt
  have hsqrtMono : Real.sqrt (H : ℝ) ≤ Real.sqrt (H + 1 : ℝ) := by
    exact Real.sqrt_le_sqrt (by norm_num)
  have hsqrtOne : 1 ≤ Real.sqrt (H + 1 : ℝ) := by
    rw [Real.one_le_sqrt]
    norm_num
  have hwidth : (binomialAnnulusWidth H : ℝ) ≤
      4 * Real.sqrt (H + 1 : ℝ) := by
    unfold binomialAnnulusWidth
    push_cast
    nlinarith
  have hcardSqrt : ((binomialAnnulus H j).card : ℝ) ≤
      8 * Real.sqrt (H + 1 : ℝ) := by nlinarith
  calc
    ((binomialAnnulus H j).card : ℝ) ^ theta ≤
        (8 * Real.sqrt (H + 1 : ℝ)) ^ theta :=
      Real.rpow_le_rpow (by positivity) hcardSqrt htheta0.le
    _ = (8 : ℝ) ^ theta * (H + 1 : ℝ) ^ (theta / 2) := by
      rw [Real.mul_rpow (by norm_num) (Real.sqrt_nonneg _)]
      rw [Real.rpow_div_two_eq_sqrt theta (by positivity)]
end CollatzEndpointTransport.FixedTotal
