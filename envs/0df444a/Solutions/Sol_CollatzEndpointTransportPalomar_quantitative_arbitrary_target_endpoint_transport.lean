-- Prove2me | solution 1 for CollatzEndpointTransportPalomar.quantitative_arbitrary_target_endpoint_transport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:17:28.234876+00:00
-- url     : https://prove2.me/submissions/ea96f59a-d257-42fa-b51d-23af2ed7016f

import Definitions.Def_CollatzEndpointTransport_Linear_RefinedArbitraryTargetEndpointTransport
import Definitions.Def_CollatzEndpointTransport_Solution
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
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_quantitativeArbitraryTargetEndpointTransportRefined
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
open CollatzEndpointTransportPalomar
open scoped Real
noncomputable section
namespace CollatzEndpointTransportPalomar
theorem _root_.solution
    {theta eta transport : ℝ}
    (htheta0 : 1 / 2 < theta)
    (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2)
    (htransport0 : 0 < transport)
    (htransport : transport < centralRenyiAsymptoticRate theta) :
    ∃ Dcut K : ℝ,
      0 < Dcut ∧ Dcut ≤ 1 ∧ 0 < K ∧
      ∀ {S : Set ℕ} {C D : ℝ},
        IsCDDense S C D →
        D ≤ Dcut →
        IsCDDense
          (endpointPullback S)
          (K * (1 + C ^ holderTargetExponent theta) *
            (D⁻¹) ^ holderScaleExponent theta)
          (transport * D) := by
  have heta1' : eta <
      CollatzEndpointTransport.FixedTotal.centralRenyiAlpha theta - 1 / 2 := by
    simpa [centralRenyiAlpha,
      CollatzEndpointTransport.FixedTotal.centralRenyiAlpha] using heta1
  have htransport' : transport <
      CollatzEndpointTransport.FixedTotal.centralRenyiAsymptoticRate theta := by
    simpa [centralRenyiAsymptoticRate,
      CollatzEndpointTransport.FixedTotal.centralRenyiAsymptoticRate] using
        htransport
  obtain ⟨Dcut, K, hDcut0, hDcut1, hK, hpull⟩ :=
    CollatzEndpointTransport.FixedTotal.quantitativeArbitraryTargetEndpointTransportRefined
      htheta0 htheta1 heta0 heta1' htransport0 htransport'
  refine ⟨Dcut, K, hDcut0, hDcut1, hK, ?_⟩
  intro S C D hS hDcut
  change CollatzEndpointTransport.QuantitativeDensity.IsCDDense S C D at hS
  change CollatzEndpointTransport.QuantitativeDensity.IsCDDense
    (CollatzEndpointTransport.QuantitativeDensity.collatzPullback S)
    (K * (1 + C ^
      CollatzEndpointTransport.FixedTotal.holderTargetExponent theta) *
      (D⁻¹) ^ CollatzEndpointTransport.FixedTotal.holderScaleExponent theta)
    (transport * D)
  exact hpull hS hDcut
end CollatzEndpointTransportPalomar
