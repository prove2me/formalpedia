-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.centralLevelRenyiInformation_le_sharp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:51:15.018292+00:00
-- url     : https://prove2.me/submissions/b1832b69-aec4-4f84-a42f-be43bef03dfb

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiPullback
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Definitions.Def_CollatzEndpointTransport_Linear_SharpCentralRenyiPullback
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_mixedFiberRenyi_le_weighted_by_card
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_centralLevelCohortSet_card_le
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_central_active_cohort_scaled_eq
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_sourceOddLevel
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralLevelCohortSet_eq_empty
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
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {M s : ℕ} {theta eta : ℝ}
    (htheta : 0 < theta) (hsM : s ≤ M) :
    centralLevelRenyiInformation M s theta eta ≤
      (3 : ℝ) ^ theta *
        ∑ u ∈ activeMixtureIndices (Finset.univ : Finset (Fin M))
            (centralLevelCohortSet M s theta eta),
          ((fixedSet (M - (u : ℕ)) s).card : ℝ) *
            fixedRenyiMoment (M - (u : ℕ)) s theta := by
  classical
  by_cases hs0 : s = 0
  · subst s
    have hempty : ∀ u : Fin M,
        centralLevelCohortSet M 0 theta eta u = ∅ := by
      intro u
      apply centralLevelCohortSet_eq_empty
      intro hadm
      exact (Nat.not_lt_zero 1) hadm.2.1
    have htarget : centralLevelEndpointSet M 0 theta eta = ∅ := by
      unfold centralLevelEndpointSet mixedTargetSet
      ext y
      constructor
      · intro hy
        rw [Finset.mem_biUnion] at hy
        rcases hy with ⟨u, hu, hy⟩
        rw [hempty u] at hy
        simp at hy
      · intro hy
        simp at hy
    have hactive :
        activeMixtureIndices (Finset.univ : Finset (Fin M))
          (centralLevelCohortSet M 0 theta eta) = ∅ := by
      ext u
      simp [activeMixtureIndices, hempty]
    simp [centralLevelRenyiInformation, htarget, hactive]
  have hs : 0 < s := Nat.pos_of_ne_zero hs0
  let U := (Finset.univ : Finset (Fin M))
  let W := centralLevelCohortSet M s theta eta
  let f := fun u : Fin M => cohortEndpoint u
  let B : ℝ := (sourceOddLevel M s).card
  have hB : 0 < B := by
    dsimp [B]
    rw [card_sourceOddLevel]
    exact_mod_cast Nat.choose_pos hsM
  have hcards : ∑ u ∈ U, ((W u).card : ℝ) ≤ B := by
    simpa [U, W, B] using
      (sum_centralLevelCohortSet_card_le
        (M := M) (theta := theta) (eta := eta) hs)
  have hmix := mixedFiberRenyi_le_weighted_by_card U W f hB htheta hcards
  let scale := (((3 : ℝ) ^ (s + 1)) ^ theta / B ^ theta)
  have hscale0 : 0 ≤ scale := by dsimp [scale]; positivity
  unfold centralLevelRenyiInformation
  change scale *
      (∑ y ∈ mixedTargetSet U W f,
        (mixedFiberCard U W f y : ℝ) ^ (1 + theta)) ≤ _
  calc
    scale *
        (∑ y ∈ mixedTargetSet U W f,
          (mixedFiberCard U W f y : ℝ) ^ (1 + theta)) ≤
      scale *
        (∑ u ∈ activeMixtureIndices U W,
          (((W u).card : ℝ) / B) ^ (-theta) *
            ∑ c ∈ W u,
              ((mapFiberCardAt (W u) (f u) c : ℕ) : ℝ) ^ theta) :=
      mul_le_mul_of_nonneg_left hmix hscale0
    _ = ∑ u ∈ activeMixtureIndices U W,
        (3 : ℝ) ^ theta *
          (((fixedSet (M - (u : ℕ)) s).card : ℝ) *
            fixedRenyiMoment (M - (u : ℕ)) s theta) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u hu
      have hadm : CentralRenyiAdmissible (M - (u : ℕ)) s theta eta := by
        have hne : (W u).Nonempty := (Finset.mem_filter.mp hu).2
        by_contra hnot
        have he := centralLevelCohortSet_eq_empty u hnot
        simp only [W, he, Finset.not_nonempty_empty] at hne
      simpa [scale, U, W, f, B, mul_assoc] using
        central_active_cohort_scaled_eq (theta := theta) (eta := eta) u hadm
    _ = (3 : ℝ) ^ theta *
        ∑ u ∈ activeMixtureIndices U W,
          ((fixedSet (M - (u : ℕ)) s).card : ℝ) *
            fixedRenyiMoment (M - (u : ℕ)) s theta := by
      rw [Finset.mul_sum]
end CollatzEndpointTransport.FixedTotal
