-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.quantitativeArbitraryTargetEndpointTransportRefined
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:14:55.020492+00:00
-- url     : https://prove2.me/submissions/0ef64364-34da-46b5-a51f-6d433b73c100

import Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralRenyiMomentTransport
import Definitions.Def_CollatzEndpointTransport_Linear_SharpCentralRenyiPullback
import Definitions.Def_CollatzEndpointTransport_Linear_RefinedArbitraryTargetEndpointTransport
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_refinedCentralRenyiShellConstant_pos
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sourceEndpointBad_div_pow_le_refined_absorbed
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_shellBad_collatzPullback_eq_sourceEndpointBad
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiAbsorption_pos
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiDenominatorFloor_pos
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiRate_pos
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiShellRate_lt_log_two
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_exists_centralRenyi_full_cutoff
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
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_IsCDDense_C_pos
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_IsCDDense_D_pos
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_IsCDDense_degrade_exponent
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_IsCDDense_mono_constant
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_card_positivePrefix
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_isCDDense_of_shell_bound
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
        QuantitativeDensity.IsCDDense S C D →
        D ≤ Dcut →
        QuantitativeDensity.IsCDDense
          (QuantitativeDensity.collatzPullback S)
          (K * (1 + C ^ holderTargetExponent theta) *
            (D⁻¹) ^ holderScaleExponent theta)
          (transport * D) := by
  have hthetaPos : 0 < theta := by linarith
  obtain ⟨Dcut, hDcut0, hDcut1, hcut⟩ :=
    exists_centralRenyi_full_cutoff
      hthetaPos heta0 htransport0 htransport
  let K := 2 * refinedCentralRenyiShellConstant theta eta transport /
    centralRenyiDenominatorFloor eta
  have hden := centralRenyiDenominatorFloor_pos hthetaPos heta0 heta1
  have hK : 0 < K := by
    dsimp [K]
    exact div_pos
      (mul_pos (by norm_num) (refinedCentralRenyiShellConstant_pos
        hthetaPos htheta1 heta0 heta1 htransport0 htransport)) hden
  refine ⟨Dcut, K, hDcut0, hDcut1, hK, ?_⟩
  intro S C D hS hDcut
  obtain ⟨hlinear, hcutLate, hcutParity⟩ :=
    hcut D hS.D_pos hDcut
  let A := refinedCentralRenyiShellConstant theta eta transport *
    (1 + C ^ holderTargetExponent theta) *
    (D⁻¹) ^ holderScaleExponent theta
  let rate := centralRenyiShellRate theta transport D
  have hA : 0 < A := by
    dsimp [A]
    have hCrho0 : 0 ≤ C ^ holderTargetExponent theta :=
      Real.rpow_nonneg hS.C_pos.le _
    exact mul_pos
      (mul_pos (refinedCentralRenyiShellConstant_pos
        hthetaPos htheta1 heta0 heta1 htransport0 htransport) (by linarith))
      (Real.rpow_pos_of_pos (inv_pos.mpr hS.D_pos) _)
  have hrate0 : 0 < rate := by
    dsimp [rate, centralRenyiShellRate]
    exact mul_pos (centralRenyiAbsorption_pos hthetaPos htransport0)
      (centralRenyiRate_pos hthetaPos hS.D_pos)
  have hrateLt : rate < Real.log 2 := by
    dsimp [rate]
    exact centralRenyiShellRate_lt_log_two
      hthetaPos htheta1 htransport0 htransport hS.D_pos
  have hshell : ∀ M : ℕ,
      ((QuantitativeDensity.shellBad
          (QuantitativeDensity.collatzPullback S) M).card : ℝ) ≤
        A * Real.exp (-rate * M) * (2 ^ M : ℝ) := by
    intro M
    rw [card_shellBad_collatzPullback_eq_sourceEndpointBad]
    have hsource := sourceEndpointBad_div_pow_le_refined_absorbed
      hS hthetaPos htheta1 heta0 heta1 htransport0 htransport
      hlinear hcutLate hcutParity M
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ M)).mp
      (by simpa [A, rate] using hsource)
  have hpull : QuantitativeDensity.IsCDDense
      (QuantitativeDensity.collatzPullback S)
      (2 * A / (2 * Real.exp (-rate) - 1))
      (rate / Real.log 2) :=
    QuantitativeDensity.isCDDense_of_shell_bound
      hA hrate0 hrateLt hshell
  have hdenBound :
      2 * Real.exp (-rate) - 1 ≥ centralRenyiDenominatorFloor eta := by
    dsimp [rate, centralRenyiDenominatorFloor]
    have hexp : Real.exp (-(eta ^ 2 / 8)) ≤
        Real.exp (-centralRenyiShellRate theta transport D) :=
      Real.exp_le_exp.mpr (by linarith)
    linarith
  have hden0 : 0 < 2 * Real.exp (-rate) - 1 := by
    exact lt_of_lt_of_le hden hdenBound
  have hconstant :
      2 * A / (2 * Real.exp (-rate) - 1) ≤
        K * (1 + C ^ holderTargetExponent theta) *
          (D⁻¹) ^ holderScaleExponent theta := by
    have hinv := (inv_le_inv₀ hden0 hden).2 hdenBound
    dsimp [K, A]
    rw [div_eq_mul_inv, div_eq_mul_inv]
    have hfront0 : 0 ≤
        2 * refinedCentralRenyiShellConstant theta eta transport *
          (1 + C ^ holderTargetExponent theta) *
          (D⁻¹) ^ holderScaleExponent theta := by
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num)
            (refinedCentralRenyiShellConstant_pos
              hthetaPos htheta1 heta0 heta1 htransport0 htransport).le)
          (add_nonneg (by norm_num) (Real.rpow_nonneg hS.C_pos.le _)))
        (Real.rpow_nonneg (inv_nonneg.mpr hS.D_pos.le) _)
    calc
      2 * (refinedCentralRenyiShellConstant theta eta transport *
            (1 + C ^ holderTargetExponent theta) *
            (D⁻¹) ^ holderScaleExponent theta) *
          (2 * Real.exp (-rate) - 1)⁻¹ =
        (2 * refinedCentralRenyiShellConstant theta eta transport *
          (1 + C ^ holderTargetExponent theta) *
          (D⁻¹) ^ holderScaleExponent theta) *
          (2 * Real.exp (-rate) - 1)⁻¹ := by ring
      _ ≤ (2 * refinedCentralRenyiShellConstant theta eta transport *
          (1 + C ^ holderTargetExponent theta) *
          (D⁻¹) ^ holderScaleExponent theta) *
          (centralRenyiDenominatorFloor eta)⁻¹ :=
        mul_le_mul_of_nonneg_left hinv hfront0
      _ = (2 * refinedCentralRenyiShellConstant theta eta transport *
          (centralRenyiDenominatorFloor eta)⁻¹) *
          (1 + C ^ holderTargetExponent theta) *
          (D⁻¹) ^ holderScaleExponent theta := by ring
  have hdegraded := hpull.degrade_exponent
    (mul_pos htransport0 hS.D_pos) hlinear
  exact hdegraded.mono_constant hconstant
end CollatzEndpointTransport.FixedTotal
