-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.fiber_le_ordinary_add_critical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:34:55.313592+00:00
-- url     : https://prove2.me/submissions/98c50651-0895-4a7f-ab43-b870e29143b4

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalEndpointTarget
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalFiberSplit
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_length
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
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumerator_prependOne
attribute [local simp] CollatzEndpointTransport.FixedTotal.wordCorrectionFrom_nil
attribute [local simp] CollatzEndpointTransport.QuantitativeDensity.card_positivePrefix
attribute [local simp] CollatzEndpointTransport.QuantitativeDensity.mem_basePullback
attribute [local simp] CollatzEndpointTransport.QuantitativeDensity.mem_collatzPullback
attribute [local simp] CollatzEndpointTransport.Terras.integerCorrection_zero



set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {E N R f : ℝ}
    (hE : 0 < E) (hN : 0 < N) (hR : 0 < R) (hf : 0 ≤ f) :
    f ≤
      E ^ 2 * N / R +
        E⁻¹ * Real.sqrt (R / N) * f * Real.sqrt f := by
  have hRN : 0 ≤ R / N := by positivity
  have hsqrtRN : 0 ≤ Real.sqrt (R / N) := Real.sqrt_nonneg _
  have hsqrtf : 0 ≤ Real.sqrt f := Real.sqrt_nonneg _
  by_cases hsmall : f ≤ E ^ 2 * N / R
  · exact hsmall.trans (le_add_of_nonneg_right (by positivity))
  · have hlarge : E ^ 2 * N / R < f := lt_of_not_ge hsmall
    have hcross : E ^ 2 * N < f * R := by
      exact (div_lt_iff₀ hR).mp (by simpa [mul_assoc] using hlarge)
    have hsq :
        E ^ 2 ≤
          (Real.sqrt (R / N) * Real.sqrt f) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hRN, Real.sq_sqrt hf]
      apply le_of_lt
      rw [div_mul_eq_mul_div]
      apply (lt_div_iff₀ hN).2
      nlinarith
    have hroot :
        E ≤ Real.sqrt (R / N) * Real.sqrt f :=
      (sq_le_sq₀ hE.le (mul_nonneg hsqrtRN hsqrtf)).mp hsq
    have hcritical :
        f ≤
          E⁻¹ * Real.sqrt (R / N) * f * Real.sqrt f := by
      calc
        f = E⁻¹ * E * f := by
          field_simp [ne_of_gt hE]
        _ ≤ E⁻¹ *
            (Real.sqrt (R / N) * Real.sqrt f) * f := by
          gcongr
        _ = E⁻¹ * Real.sqrt (R / N) * f * Real.sqrt f := by
          ring
    exact hcritical.trans (le_add_of_nonneg_left (by positivity))
end CollatzEndpointTransport.FixedTotal
