-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.centralRenyiMomentInverse_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:41:55.961822+00:00
-- url     : https://prove2.me/submissions/6464c954-f0c1-4e49-8715-413a085abb2a

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiShell
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalNonlinearShell
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiPullback
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiAbsorption_lt_one
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiRate_pos
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiRate_inv_le
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
open Nat Finset
open scoped Real Topology
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.centralPullbackSourceCodeDecidableEq
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {theta transport D : ℝ}
    (htheta0 : 0 < theta)
    (htransport0 : 0 < transport)
    (htransport : transport < centralRenyiAsymptoticRate theta)
    (hD0 : 0 < D)
    (hlinear : transport * D ≤
      centralRenyiShellRate theta transport D / Real.log 2) :
    ((((1 - centralRenyiAbsorption theta transport) *
      centralRenyiRate theta D / 6)⁻¹) ^ 6) ≤
      centralRenyiInverseRateFactor theta transport * (D⁻¹) ^ 6 := by
  let zeta := centralRenyiAbsorption theta transport
  let r := centralRenyiRate theta D
  have hz1 := centralRenyiAbsorption_lt_one htheta0 htransport
  have hr0 := centralRenyiRate_pos htheta0 hD0
  have hrInv := centralRenyiRate_inv_le htheta0 htransport0 hD0 hlinear
  have hcoef0 : 0 ≤ 6 / (1 - zeta) :=
    div_nonneg (by norm_num) (sub_nonneg.mpr hz1.le)
  have hcore :
      (((1 - zeta) * r / 6)⁻¹) ≤
        (6 / (1 - zeta)) *
          (zeta / (transport * Real.log 2)) * D⁻¹ := by
    rw [show (((1 - zeta) * r / 6)⁻¹) =
        (6 / (1 - zeta)) * r⁻¹ by
      field_simp [sub_ne_zero.mpr hz1.ne, hr0.ne']]
    have hmul := mul_le_mul_of_nonneg_left hrInv hcoef0
    simpa [zeta, r, mul_assoc] using hmul
  have hden0 : 0 ≤ (1 - zeta) * r / 6 :=
    div_nonneg (mul_nonneg (sub_nonneg.mpr hz1.le) hr0.le) (by norm_num)
  have hpow := pow_le_pow_left₀ (inv_nonneg.mpr hden0) hcore 6
  calc
    ((((1 - centralRenyiAbsorption theta transport) *
        centralRenyiRate theta D / 6)⁻¹) ^ 6) ≤
        ((6 / (1 - zeta)) *
          (zeta / (transport * Real.log 2)) * D⁻¹) ^ 6 := by
      simpa [zeta, r] using hpow
    _ = centralRenyiInverseRateFactor theta transport * (D⁻¹) ^ 6 := by
      unfold centralRenyiInverseRateFactor
      dsimp [zeta]
      rw [mul_pow]
end CollatzEndpointTransport.FixedTotal
