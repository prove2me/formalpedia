-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.shell_admissible_fixed_total_aggregate_le_sharp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:51:03.425025+00:00
-- url     : https://prove2.me/submissions/dd42785a-517e-45ac-88f6-67b434a23f16

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiPullback
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Definitions.Def_CollatzEndpointTransport_Linear_SharpCentralRenyiPullback
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedSourceWeight_mul_fixedRenyiMoment_le_sharp
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_rpow_one_sub_le_card_rpow
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_fixedSourceWeight_shellAdmissible_le_one
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralMomentConstant_pos
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedSourceWeight_nonneg
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
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {M N : ℕ} {theta eta : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2)
    (hN : 0 < N) :
    (∑ s ∈ shellAdmissibleLengthSet M N theta eta,
        fixedSourceWeight N s * fixedRenyiMoment N s theta) ≤
      centralMomentConstant theta eta * (N + 1 : ℝ) *
        (M + 1 : ℝ) ^ theta := by
  classical
  let U := shellAdmissibleLengthSet M N theta eta
  let K := centralMomentConstant theta eta
  have hK0 : 0 ≤ K :=
    (centralMomentConstant_pos htheta0 htheta1 heta0 heta1).le
  have hlevel : ∀ s ∈ U,
      fixedSourceWeight N s * fixedRenyiMoment N s theta ≤
        K * (N + 1 : ℝ) *
          (fixedSourceWeight N s) ^ (1 - theta) := by
    intro s hs
    have hadm : CentralRenyiAdmissible N s theta eta :=
      (Finset.mem_filter.mp hs).2
    exact fixedSourceWeight_mul_fixedRenyiMoment_le_sharp
      htheta0 htheta1 heta0 heta1
      hadm.1 hadm.2.1 hadm.2.2.1 hadm.2.2.2.1
      hadm.2.2.2.2.1 hadm.2.2.2.2.2
  have hpowers :
      ∑ s ∈ U, (fixedSourceWeight N s) ^ (1 - theta) ≤
        (U.card : ℝ) ^ theta :=
    sum_rpow_one_sub_le_card_rpow U
      (fun s => fixedSourceWeight N s) htheta0 htheta1
      (fun s hs => fixedSourceWeight_nonneg N s)
      (by simpa [U] using
        sum_fixedSourceWeight_shellAdmissible_le_one hN theta eta)
  have hsub : U ⊆ Finset.range (M + 1) := by
    intro s hs
    exact (Finset.mem_filter.mp hs).1
  have hcard : (U.card : ℝ) ≤ (M + 1 : ℝ) := by
    have hc := Finset.card_le_card hsub
    simpa using (show (U.card : ℝ) ≤ ((Finset.range (M + 1)).card : ℝ) by
      exact_mod_cast hc)
  have hcardPow : (U.card : ℝ) ^ theta ≤ (M + 1 : ℝ) ^ theta :=
    Real.rpow_le_rpow (by positivity) hcard htheta0.le
  calc
    (∑ s ∈ shellAdmissibleLengthSet M N theta eta,
        fixedSourceWeight N s * fixedRenyiMoment N s theta) ≤
      ∑ s ∈ U, K * (N + 1 : ℝ) *
        (fixedSourceWeight N s) ^ (1 - theta) := by
      simpa [U] using Finset.sum_le_sum hlevel
    _ = K * (N + 1 : ℝ) *
        ∑ s ∈ U, (fixedSourceWeight N s) ^ (1 - theta) := by
      rw [Finset.mul_sum]
    _ ≤ K * (N + 1 : ℝ) * (U.card : ℝ) ^ theta :=
      mul_le_mul_of_nonneg_left hpowers
        (mul_nonneg hK0 (by positivity))
    _ ≤ K * (N + 1 : ℝ) * (M + 1 : ℝ) ^ theta :=
      mul_le_mul_of_nonneg_left hcardPow
        (mul_nonneg hK0 (by positivity))
end CollatzEndpointTransport.FixedTotal
