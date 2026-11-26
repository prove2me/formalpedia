-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.sum_fixedLengthProbability_rpow_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:51:33.303817+00:00
-- url     : https://prove2.me/submissions/babc9f52-529d-4544-a340-6d7ebcb7b989

import Definitions.Def_CollatzEndpointTransport_Linear_FixedSizeCentralRenyiMoment
import Definitions.Def_CollatzEndpointTransport_Linear_FractionalBinomialMassBound
import Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralAggregate
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedLengthProbability_eq_symmetricBinomialMass
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_normalizedReverseLift_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseLiftNumerator_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseLiftNumerator_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseMomentMajorant_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseMomentMajorant_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_fractional_symmetricBinomialMass_le
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumerator_prependOne
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.normalizedReverseLift_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.reverseLiftNumerator_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.reverseLiftNumerator_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.reverseMomentMajorant_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.reverseMomentMajorant_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumerator_prependOne



set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
set_option maxHeartbeats 400000
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {N : ℕ} {theta : ℝ}
    (hN : 1 < N) (htheta0 : 0 < theta) (htheta1 : theta < 1) :
    (∑ s ∈ Finset.Icc 1 N,
        (fixedLengthProbability N s) ^ (1 - theta)) ≤
      fractionalBinomialMassConstant theta *
        (N : ℝ) ^ (theta / 2) := by
  have hbinomial := sum_fractional_symmetricBinomialMass_le
    (H := N - 1) (by omega : 0 < N - 1) htheta0 htheta1
  have hbinomial' :
      (∑ k ∈ Finset.range N,
          (symmetricBinomialMass (N - 1) k) ^ (1 - theta)) ≤
        fractionalBinomialMassConstant theta *
          (N : ℝ) ^ (theta / 2) := by
    simpa [Nat.sub_add_cancel (by omega : 1 ≤ N),
      Nat.cast_sub (by omega : 1 ≤ N)] using hbinomial
  have hreindex :
      (∑ s ∈ Finset.Icc 1 N,
          (symmetricBinomialMass (N - 1) (s - 1)) ^ (1 - theta)) =
        ∑ k ∈ Finset.range N,
          (symmetricBinomialMass (N - 1) k) ^ (1 - theta) := by
    rw [← Finset.Ico_add_one_right_eq_Icc]
    rw [Finset.sum_Ico_eq_sum_range]
    simp
  calc
    (∑ s ∈ Finset.Icc 1 N,
        (fixedLengthProbability N s) ^ (1 - theta)) =
        ∑ s ∈ Finset.Icc 1 N,
          (symmetricBinomialMass (N - 1) (s - 1)) ^ (1 - theta) := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [fixedLengthProbability_eq_symmetricBinomialMass
        (by omega) (Finset.mem_Icc.mp hs).1]
    _ = ∑ k ∈ Finset.range N,
          (symmetricBinomialMass (N - 1) k) ^ (1 - theta) := hreindex
    _ ≤ fractionalBinomialMassConstant theta *
          (N : ℝ) ^ (theta / 2) := hbinomial'
end CollatzEndpointTransport.FixedTotal
