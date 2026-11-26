-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.refinedCentralRenyiMomentInverse_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:51:51.406805+00:00
-- url     : https://prove2.me/submissions/7a2f117e-9784-405e-ae3d-5497a7d99ad3

import Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralRenyiMomentTransport
import Definitions.Def_CollatzEndpointTransport_Linear_SharpCentralRenyiPullback
import Definitions.Def_CollatzEndpointTransport_Linear_RefinedArbitraryTargetEndpointTransport
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_holderScaleExponent_pos
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiAbsorption_lt_one
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiAbsorption_pos
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiRate_inv_le
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiRate_pos
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_mem_centralSourceSet_inl
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_mem_centralSourceSet_inr
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_mem_sourceLateFirstOdd_inl
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_mem_sourceLateFirstOdd_inr
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
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_wordCorrectionFrom_nil
import Theorems.Thm_CollatzEndpointTransport_OptimizedLinearPullback_psi_zero
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_card_positivePrefix
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_mem_basePullback
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_mem_collatzPullback
import Theorems.Thm_CollatzEndpointTransport_Terras_integerCorrection_zero
attribute [local simp] CollatzEndpointTransport.FixedTotal.encodeBlocks_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.encodeBlocks_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.mem_centralSourceSet_inl
attribute [local simp] CollatzEndpointTransport.FixedTotal.mem_centralSourceSet_inr
attribute [local simp] CollatzEndpointTransport.FixedTotal.mem_sourceLateFirstOdd_inl
attribute [local simp] CollatzEndpointTransport.FixedTotal.mem_sourceLateFirstOdd_inr
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
attribute [local simp] CollatzEndpointTransport.FixedTotal.wordCorrectionFrom_nil
attribute [local simp] CollatzEndpointTransport.OptimizedLinearPullback.psi_zero
attribute [local simp] CollatzEndpointTransport.QuantitativeDensity.card_positivePrefix
attribute [local simp] CollatzEndpointTransport.QuantitativeDensity.mem_basePullback
attribute [local simp] CollatzEndpointTransport.QuantitativeDensity.mem_collatzPullback
attribute [local simp] CollatzEndpointTransport.Terras.integerCorrection_zero



set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {theta transport D : ℝ}
    (htheta : 0 < theta)
    (htransport0 : 0 < transport)
    (htransport : transport < centralRenyiAsymptoticRate theta)
    (hD0 : 0 < D)
    (hlinear : transport * D ≤
      centralRenyiShellRate theta transport D / Real.log 2) :
    (((1 - centralRenyiAbsorption theta transport) *
        centralRenyiRate theta D / holderScaleExponent theta) ^
          (-holderScaleExponent theta)) ≤
      refinedCentralRenyiInverseRateFactor theta transport *
        (D⁻¹) ^ holderScaleExponent theta := by
  let B := holderScaleExponent theta
  let zeta := centralRenyiAbsorption theta transport
  let r := centralRenyiRate theta D
  let q := (B / (1 - zeta)) *
    (zeta / (transport * Real.log 2))
  have hB : 0 < B := holderScaleExponent_pos htheta
  have hz0 : 0 < zeta := centralRenyiAbsorption_pos htheta htransport0
  have hz1 : zeta < 1 := centralRenyiAbsorption_lt_one htheta htransport
  have hr0 : 0 < r := centralRenyiRate_pos htheta hD0
  have hrInv := centralRenyiRate_inv_le htheta htransport0 hD0 hlinear
  have hcoef0 : 0 ≤ B / (1 - zeta) :=
    div_nonneg hB.le (sub_nonneg.mpr hz1.le)
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hcore : (((1 - zeta) * r / B)⁻¹) ≤ q * D⁻¹ := by
    rw [show (((1 - zeta) * r / B)⁻¹) =
        (B / (1 - zeta)) * r⁻¹ by
      field_simp [sub_ne_zero.mpr hz1.ne, hr0.ne', hB.ne']]
    have hmul := mul_le_mul_of_nonneg_left hrInv hcoef0
    simpa [q, zeta, r, B, mul_assoc] using hmul
  have hbase0 : 0 ≤ (1 - zeta) * r / B :=
    (div_pos (mul_pos (sub_pos.mpr hz1) hr0) hB).le
  calc
    (((1 - centralRenyiAbsorption theta transport) *
        centralRenyiRate theta D / holderScaleExponent theta) ^
          (-holderScaleExponent theta)) =
        (((1 - zeta) * r / B)⁻¹) ^ B := by
      dsimp [zeta, r, B]
      rw [Real.rpow_neg_eq_inv_rpow]
    _ ≤ (q * D⁻¹) ^ B :=
      Real.rpow_le_rpow (inv_nonneg.mpr hbase0) hcore hB.le
    _ = q ^ B * (D⁻¹) ^ B := by
      rw [Real.mul_rpow hq0 (inv_nonneg.mpr hD0.le)]
    _ = refinedCentralRenyiInverseRateFactor theta transport *
          (D⁻¹) ^ holderScaleExponent theta := by
      rfl
end CollatzEndpointTransport.FixedTotal
