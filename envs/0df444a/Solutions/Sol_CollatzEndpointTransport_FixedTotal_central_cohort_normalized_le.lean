-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.central_cohort_normalized_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:42:03.24486+00:00
-- url     : https://prove2.me/submissions/2844a6f6-371e-4a22-b8ea-d80267d162d5

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Definitions.Def_CollatzEndpointTransport_Linear_FiniteFiberMixture
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalActualEndpointMoment
import Definitions.Def_CollatzEndpointTransport_Common_TerrasPrefixEvents
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiShell
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_cohortRenyiSourceMoment_le_fixed
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralLevelCohortSet_eq_fixed
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralLevelCohortSet_eq_empty
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedSet_card_le_sourceOddLevel
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_numerator_div_global_le_card_mul_moment
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_fixedSet
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



set_option autoImplicit false
set_option maxHeartbeats 4000000
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.centralShellCompositionDecidableEq
attribute [local instance] CollatzEndpointTransport.FixedTotal.centralRenyiAdmissibleDecidable
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {M s : ℕ} {theta eta : ℝ} (u : Fin M)
    (htheta0 : 0 < theta) (htheta1 : theta < 1) :
    (((3 : ℝ) ^ s) ^ theta /
        (((sourceOddLevel M s).card : ℝ) ^ theta)) *
      (∑ c ∈ centralLevelCohortSet M s theta eta u,
        ((mapFiberCardAt
          (centralLevelCohortSet M s theta eta u)
          (cohortEndpoint u) c : ℕ) : ℝ) ^ theta) ≤
    if CentralRenyiAdmissible (M - (u : ℕ)) s theta eta then
      ((fixedSet (M - (u : ℕ)) s).card : ℝ) *
        fixedRenyiMoment (M - (u : ℕ)) s theta
    else 0 := by
  classical
  by_cases hadm : CentralRenyiAdmissible (M - (u : ℕ)) s theta eta
  · rw [if_pos hadm]
    rw [centralLevelCohortSet_eq_fixed u hadm]
    have hs : 0 < s := by exact (hadm.2.1.trans' (by omega))
    have hcard : 0 < (fixedSet (M - (u : ℕ)) s).card := by
      have hN : 0 < M - (u : ℕ) := by omega
      rw [card_fixedSet _ _ hN hs]
      exact Nat.choose_pos
        (Nat.sub_le_sub_right (Nat.le_of_lt hadm.2.2.1) 1)
    have hB := fixedSet_card_le_sourceOddLevel u hs
    have hbridge := cohortRenyiSourceMoment_le_fixed M u s htheta0.le
    have hnorm := numerator_div_global_le_card_mul_moment
      htheta0.le hcard hB
    calc
      (((3 : ℝ) ^ s) ^ theta /
          (((sourceOddLevel M s).card : ℝ) ^ theta)) *
        (∑ c ∈ fixedSet (M - (u : ℕ)) s,
          ((mapFiberCardAt
            (fixedSet (M - (u : ℕ)) s)
            (cohortEndpoint u) c : ℕ) : ℝ) ^ theta) =
        cohortRenyiSourceMoment M u s theta /
          (((sourceOddLevel M s).card : ℝ) ^ theta) := by
        unfold cohortRenyiSourceMoment
        ring
      _ ≤ fixedRenyiNumerator (M - (u : ℕ)) s theta /
          (((sourceOddLevel M s).card : ℝ) ^ theta) := by
        exact div_le_div_of_nonneg_right hbridge (by positivity)
      _ ≤ ((fixedSet (M - (u : ℕ)) s).card : ℝ) *
          fixedRenyiMoment (M - (u : ℕ)) s theta := hnorm
  · rw [if_neg hadm]
    rw [centralLevelCohortSet_eq_empty u hadm]
    simp
end CollatzEndpointTransport.FixedTotal
