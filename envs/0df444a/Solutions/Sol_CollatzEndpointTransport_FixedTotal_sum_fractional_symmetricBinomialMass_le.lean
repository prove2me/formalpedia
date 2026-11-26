-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.sum_fractional_symmetricBinomialMass_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:49:52.953828+00:00
-- url     : https://prove2.me/submissions/5098f924-c183-4c29-a1c6-8db3c8594e52

import Definitions.Def_CollatzEndpointTransport_Linear_FractionalBinomialMass
import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_CollatzEndpointTransport_Linear_FractionalBinomialMassBound
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_fractional_symmetricBinomialMass_annulus_le
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_annular_fractional_decay_le
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_binomialAnnuli


set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
set_option maxHeartbeats 400000
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {H : ℕ} {theta : ℝ}
    (hH : 0 < H) (htheta0 : 0 < theta) (htheta1 : theta < 1) :
    (∑ k ∈ Finset.range (H + 1),
        (symmetricBinomialMass H k) ^ (1 - theta)) ≤
      fractionalBinomialMassConstant theta *
        (H + 1 : ℝ) ^ (theta / 2) := by
  let scale := (8 : ℝ) ^ theta * (H + 1 : ℝ) ^ (theta / 2)
  have hscale0 : 0 ≤ scale := by
    dsimp [scale]
    positivity
  have hannulus : ∀ j ∈ Finset.range (H + 1),
      (∑ k ∈ binomialAnnulus H j,
          (symmetricBinomialMass H k) ^ (1 - theta)) ≤
        scale * (2 * Real.exp (-2 * (j : ℝ) ^ 2)) ^ (1 - theta) := by
    intro j hj
    simpa [scale] using sum_fractional_symmetricBinomialMass_annulus_le
      (H := H) (j := j) hH htheta0 htheta1
  have hdecay := sum_annular_fractional_decay_le H htheta0 htheta1
  calc
    (∑ k ∈ Finset.range (H + 1),
        (symmetricBinomialMass H k) ^ (1 - theta)) =
        ∑ j ∈ Finset.range (H + 1),
          ∑ k ∈ binomialAnnulus H j,
            (symmetricBinomialMass H k) ^ (1 - theta) :=
      sum_binomialAnnuli _
    _ ≤ ∑ j ∈ Finset.range (H + 1),
          scale * (2 * Real.exp (-2 * (j : ℝ) ^ 2)) ^ (1 - theta) :=
      Finset.sum_le_sum hannulus
    _ = scale *
          ∑ j ∈ Finset.range (H + 1),
            (2 * Real.exp (-2 * (j : ℝ) ^ 2)) ^ (1 - theta) := by
      rw [Finset.mul_sum]
    _ ≤ scale * ((2 : ℝ) ^ (1 - theta) *
          (1 - Real.exp (-2 * (1 - theta)))⁻¹) :=
      mul_le_mul_of_nonneg_left hdecay hscale0
    _ = fractionalBinomialMassConstant theta *
          (H + 1 : ℝ) ^ (theta / 2) := by
      unfold fractionalBinomialMassConstant
      dsimp [scale]
      ring
end CollatzEndpointTransport.FixedTotal
