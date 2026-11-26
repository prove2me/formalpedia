-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.cohortRenyiSourceMoment_eq_fixed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:38:36.368224+00:00
-- url     : https://prove2.me/submissions/702aa70c-0234-4ff1-a4de-da9a25a1cdc8

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Definitions.Def_CollatzEndpointTransport_Linear_FiniteFiberMixture
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalActualEndpointMoment
import Definitions.Def_CollatzEndpointTransport_Common_TerrasPrefixEvents
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiShell
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_mapFiberCardAt_rpow_eq
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_cohortEndpoint_mapFiberCardAt_eq_numerator
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_cohortNumerator_mapFiber_eq_residueFiber
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
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.centralEndpointCompositionDecidableEq
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    (M : ℕ) (u : Fin M) (s : ℕ) (theta : ℝ) :
    cohortRenyiSourceMoment M u s theta =
      fixedRenyiNumerator (M - (u : ℕ)) s theta := by
  let W := fixedSet (M - (u : ℕ)) s
  let f := cohortEndpoint u
  let g : Composition (M - (u : ℕ)) → Fin (3 ^ s) :=
    cohortNumeratorResidue
  have hsum :
      (∑ c ∈ W, ((mapFiberCardAt W f c : ℕ) : ℝ) ^ theta) =
        ∑ c ∈ W, ((mapFiberCardAt W g c : ℕ) : ℝ) ^ theta := by
    apply Finset.sum_congr rfl
    intro c hc
    rw [cohortEndpoint_mapFiberCardAt_eq_numerator u hc]
  have hreindex :
      (∑ c ∈ W, ((mapFiberCardAt W g c : ℕ) : ℝ) ^ theta) =
        ∑ a : Fin (3 ^ s),
          (fixedFiberCard (M - (u : ℕ)) s a : ℝ) *
            (fixedFiberCard (M - (u : ℕ)) s a : ℝ) ^ theta := by
    rw [sum_mapFiberCardAt_rpow_eq W g theta]
    apply Finset.sum_congr rfl
    intro a ha
    rw [cohortNumerator_mapFiber_eq_residueFiber]
    rfl
  calc
    cohortRenyiSourceMoment M u s theta =
        ((3 : ℝ) ^ s) ^ theta *
          ∑ c ∈ W, ((mapFiberCardAt W f c : ℕ) : ℝ) ^ theta := by rfl
    _ = ((3 : ℝ) ^ s) ^ theta *
          ∑ c ∈ W, ((mapFiberCardAt W g c : ℕ) : ℝ) ^ theta := by
      rw [hsum]
    _ = fixedRenyiNumerator (M - (u : ℕ)) s theta := by
      rw [hreindex]
      simp [fixedRenyiNumerator, Nat.cast_pow]
end CollatzEndpointTransport.FixedTotal
