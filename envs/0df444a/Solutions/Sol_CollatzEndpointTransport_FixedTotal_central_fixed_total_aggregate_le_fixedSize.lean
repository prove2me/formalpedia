-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.central_fixed_total_aggregate_le_fixedSize
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:02:11.499373+00:00
-- url     : https://prove2.me/submissions/7c6c23ca-7df8-464f-ac56-23a0cb4639ed

import Definitions.Def_CollatzEndpointTransport_Linear_FixedSizeCentralRenyiMoment
import Definitions.Def_CollatzEndpointTransport_Linear_FractionalBinomialMassBound
import Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralAggregate
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_fixedSourceWeight_rpow_central_le
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedSizeCentralMomentConstant_pos
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedSourceWeight_mul_fixedRenyiMoment_le_fixedSize
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_normalizedReverseLift_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseLiftNumerator_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseLiftNumerator_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseMomentMajorant_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseMomentMajorant_nil
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
    {N : ℕ} {theta eta : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2)
    (hN : 2 < N)
    (hsizePi :
      2 * eta ≤ centralRenyiGap theta eta * ((N : ℝ) - 1))
    (hsizeDrift :
      (1 / 2 : ℝ) ≤
        (Real.log 2 / Real.log 3 - (1 / 2 + eta)) * N)
    (hinterior :
      ∀ s ∈ centralLengthSet N eta, 1 < s ∧ s < N) :
    (∑ s ∈ centralLengthSet N eta,
        fixedSourceWeight N s * fixedRenyiMoment N s theta) ≤
      (fixedSizeCentralMomentConstant theta eta *
          fractionalBinomialMassConstant theta) *
        (N : ℝ) ^ (theta / 2) := by
  classical
  let K := fixedSizeCentralMomentConstant theta eta
  have hK0 : 0 ≤ K :=
    (fixedSizeCentralMomentConstant_pos htheta0 htheta1 heta0 heta1).le
  have hlevel : ∀ s ∈ centralLengthSet N eta,
      fixedSourceWeight N s * fixedRenyiMoment N s theta ≤
        K * (fixedSourceWeight N s) ^ (1 - theta) := by
    intro s hs
    have hsData := hinterior s hs
    have hcen := (Finset.mem_filter.mp hs).2
    exact fixedSourceWeight_mul_fixedRenyiMoment_le_fixedSize
      htheta0 htheta1 heta0 heta1 (by omega)
      hsData.1 hsData.2 hcen hsizePi hsizeDrift
  have hpowers := sum_fixedSourceWeight_rpow_central_le
    (N := N) (theta := theta) (eta := eta) (by omega) htheta0 htheta1
  calc
    (∑ s ∈ centralLengthSet N eta,
        fixedSourceWeight N s * fixedRenyiMoment N s theta) ≤
        ∑ s ∈ centralLengthSet N eta,
          K * (fixedSourceWeight N s) ^ (1 - theta) :=
      Finset.sum_le_sum hlevel
    _ = K * ∑ s ∈ centralLengthSet N eta,
          (fixedSourceWeight N s) ^ (1 - theta) := by
      rw [Finset.mul_sum]
    _ ≤ K * (fractionalBinomialMassConstant theta *
          (N : ℝ) ^ (theta / 2)) :=
      mul_le_mul_of_nonneg_left hpowers hK0
    _ = (fixedSizeCentralMomentConstant theta eta *
          fractionalBinomialMassConstant theta) *
        (N : ℝ) ^ (theta / 2) := by
      dsimp [K]
      ring
end CollatzEndpointTransport.FixedTotal
