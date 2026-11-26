-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.sum_fixedSourceWeight_rpow_central_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:53:33.433826+00:00
-- url     : https://prove2.me/submissions/47cb0fae-5e0a-47b3-8f3d-2dcb8919ecd4

import Definitions.Def_CollatzEndpointTransport_Linear_FixedSizeCentralRenyiMoment
import Definitions.Def_CollatzEndpointTransport_Linear_FractionalBinomialMassBound
import Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralAggregate
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedSourceWeight_eq_half_fixedLengthProbability
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_fixedLengthProbability_rpow_le
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedSourceWeight_nonneg


set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
set_option maxHeartbeats 400000
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {N : ℕ} {theta eta : ℝ}
    (hN : 1 < N) (htheta0 : 0 < theta) (htheta1 : theta < 1) :
    (∑ s ∈ centralLengthSet N eta,
        (fixedSourceWeight N s) ^ (1 - theta)) ≤
      fractionalBinomialMassConstant theta *
        (N : ℝ) ^ (theta / 2) := by
  classical
  have hsub : centralLengthSet N eta ⊆ Finset.Icc 1 N := by
    intro s hs
    exact (Finset.mem_filter.mp hs).1
  have hrestrict :
      (∑ s ∈ centralLengthSet N eta,
          (fixedSourceWeight N s) ^ (1 - theta)) ≤
        ∑ s ∈ Finset.Icc 1 N,
          (fixedSourceWeight N s) ^ (1 - theta) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun s hs hnot => Real.rpow_nonneg (fixedSourceWeight_nonneg N s) _)
  have hpoint : ∀ s ∈ Finset.Icc 1 N,
      (fixedSourceWeight N s) ^ (1 - theta) ≤
        (fixedLengthProbability N s) ^ (1 - theta) := by
    intro s hs
    have hprob0 : 0 ≤ fixedLengthProbability N s := by
      unfold fixedLengthProbability
      positivity
    have hhalf := fixedSourceWeight_eq_half_fixedLengthProbability
      (N := N) (s := s) (by omega : 0 < N)
    have hweightLe : fixedSourceWeight N s ≤ fixedLengthProbability N s := by
      rw [hhalf]
      linarith
    exact Real.rpow_le_rpow (fixedSourceWeight_nonneg N s)
      hweightLe (by linarith)
  calc
    (∑ s ∈ centralLengthSet N eta,
        (fixedSourceWeight N s) ^ (1 - theta)) ≤
        ∑ s ∈ Finset.Icc 1 N,
          (fixedSourceWeight N s) ^ (1 - theta) := hrestrict
    _ ≤ ∑ s ∈ Finset.Icc 1 N,
          (fixedLengthProbability N s) ^ (1 - theta) :=
      Finset.sum_le_sum hpoint
    _ ≤ fractionalBinomialMassConstant theta *
          (N : ℝ) ^ (theta / 2) :=
      sum_fixedLengthProbability_rpow_le hN htheta0 htheta1
end CollatzEndpointTransport.FixedTotal
