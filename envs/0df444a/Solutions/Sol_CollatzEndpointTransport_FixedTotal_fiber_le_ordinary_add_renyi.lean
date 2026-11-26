-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.fiber_le_ordinary_add_renyi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:34:18.887565+00:00
-- url     : https://prove2.me/submissions/df1b5ee3-0dd2-45cc-ba0e-f5ad6d7caf45

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Definitions.Def_CollatzEndpointTransport_Linear_FiniteFiberMixture
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalActualEndpointMoment
import Definitions.Def_CollatzEndpointTransport_Common_TerrasPrefixEvents
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiShell
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_mem_centralSourceSet_inr
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_mem_centralSourceSet_inl
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_mem_sourceLateFirstOdd_inl
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_mem_sourceLateFirstOdd_inr
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_nil
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
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_wordCorrectionFrom_nil
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_card_positivePrefix
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_mem_basePullback
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_mem_collatzPullback
import Theorems.Thm_CollatzEndpointTransport_Terras_integerCorrection_zero
attribute [local simp] CollatzEndpointTransport.FixedTotal.encodeBlocks_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.encodeBlocks_nil
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
attribute [local simp] CollatzEndpointTransport.FixedTotal.wordCorrectionFrom_nil
attribute [local simp] CollatzEndpointTransport.QuantitativeDensity.card_positivePrefix
attribute [local simp] CollatzEndpointTransport.QuantitativeDensity.mem_basePullback
attribute [local simp] CollatzEndpointTransport.QuantitativeDensity.mem_collatzPullback
attribute [local simp] CollatzEndpointTransport.Terras.integerCorrection_zero


attribute [local simp] CollatzEndpointTransport.FixedTotal.mem_centralSourceSet_inr
attribute [local simp] CollatzEndpointTransport.FixedTotal.mem_centralSourceSet_inl
attribute [local simp] CollatzEndpointTransport.FixedTotal.mem_sourceLateFirstOdd_inl
attribute [local simp] CollatzEndpointTransport.FixedTotal.mem_sourceLateFirstOdd_inr

set_option autoImplicit false
set_option maxHeartbeats 4000000
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {Q N R f theta : ℝ}
    (hQ : 0 < Q) (hN : 0 < N) (hR : 0 < R)
    (hf : 0 ≤ f) (htheta : 0 < theta) :
    f ≤ Q * N / R +
      Q ^ (-theta) * (R / N) ^ theta * f ^ (1 + theta) := by
  by_cases hsmall : f ≤ Q * N / R
  · exact hsmall.trans (le_add_of_nonneg_right (by positivity))
  · have hlarge : Q * N / R < f := lt_of_not_ge hsmall
    have hfpos : 0 < f := lt_of_le_of_lt (by positivity) hlarge
    have hprod : Q * N < f * R := by
      exact (div_lt_iff₀ hR).mp (by simpa [mul_assoc] using hlarge)
    have hratio : 1 < (R / N) * f / Q := by
      rw [lt_div_iff₀ hQ]
      rw [show (R / N) * f = f * R / N by ring]
      exact (lt_div_iff₀ hN).2 (by nlinarith)
    have hratioPow : 1 ≤ (((R / N) * f / Q) ^ theta) :=
      Real.one_le_rpow hratio.le htheta.le
    have heq :
        f * (((R / N) * f / Q) ^ theta) =
          Q ^ (-theta) * (R / N) ^ theta * f ^ (1 + theta) := by
      rw [Real.div_rpow (mul_nonneg (by positivity) hf) hQ.le]
      rw [Real.mul_rpow (by positivity) hf]
      rw [Real.rpow_neg hQ.le]
      rw [Real.rpow_add hfpos]
      rw [Real.rpow_one]
      field_simp [(Real.rpow_pos_of_pos hQ theta).ne']
    have hheavy :
        f ≤ Q ^ (-theta) * (R / N) ^ theta * f ^ (1 + theta) := by
      calc
        f = f * 1 := by ring
        _ ≤ f * (((R / N) * f / Q) ^ theta) :=
          mul_le_mul_of_nonneg_left hratioPow hf
        _ = _ := heq
    exact hheavy.trans (le_add_of_nonneg_left (by positivity))
end CollatzEndpointTransport.FixedTotal
