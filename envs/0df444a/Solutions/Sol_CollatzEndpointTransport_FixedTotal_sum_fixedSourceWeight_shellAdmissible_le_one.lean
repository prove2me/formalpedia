-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.sum_fixedSourceWeight_shellAdmissible_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:48:03.68786+00:00
-- url     : https://prove2.me/submissions/a43605f1-6759-42f8-990e-9c6a582858cb

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiPullback
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Definitions.Def_CollatzEndpointTransport_Linear_SharpCentralRenyiPullback
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
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_fixedSet
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
    {M N : ℕ} (hN : 0 < N) (theta eta : ℝ) :
    ∑ s ∈ shellAdmissibleLengthSet M N theta eta,
        fixedSourceWeight N s ≤ 1 := by
  classical
  let U := shellAdmissibleLengthSet M N theta eta
  have hsub : U ⊆ Finset.Icc 1 N := by
    intro s hs
    have hadm : CentralRenyiAdmissible N s theta eta :=
      (Finset.mem_filter.mp hs).2
    exact Finset.mem_Icc.mpr
      ⟨Nat.le_of_lt hadm.2.1, Nat.le_of_lt hadm.2.2.1⟩
  have hcardsNat :
      ∑ s ∈ U, (fixedSet N s).card ≤
        ∑ s ∈ Finset.Icc 1 N, (fixedSet N s).card :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun s _ _ => Nat.zero_le (fixedSet N s).card)
  have hpartition :
      ∑ s ∈ Finset.Icc 1 N, (fixedSet N s).card =
        Fintype.card (Composition N) := by
    simpa using sum_fixedSet N hN (fun _ => 1)
  have hcards :
      (∑ s ∈ U, ((fixedSet N s).card : ℝ)) ≤ (2 : ℝ) ^ N := by
    have hle : ∑ s ∈ U, (fixedSet N s).card ≤ 2 ^ N := by
      calc
        ∑ s ∈ U, (fixedSet N s).card ≤
            ∑ s ∈ Finset.Icc 1 N, (fixedSet N s).card := hcardsNat
        _ = Fintype.card (Composition N) := hpartition
        _ = 2 ^ (N - 1) := composition_card N
        _ ≤ 2 ^ N := pow_le_pow_right' (by norm_num : (1 : ℕ) ≤ 2)
          (Nat.sub_le N 1)
    exact_mod_cast hle
  unfold fixedSourceWeight
  rw [← Finset.sum_div]
  exact (div_le_one (by positivity : (0 : ℝ) < (2 : ℝ) ^ N)).2 hcards
end CollatzEndpointTransport.FixedTotal
