-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.minor_hits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:08:28.674103+00:00
-- url     : https://prove2.me/submissions/043c4cf6-47d7-4940-8794-077bf197c26b

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementAB
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BiHomSum
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DegLESum
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_FinsuppStepInduction
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_hits_col
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_hits_row

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (jetPair)
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution : MinorHits := by
  classical
  intro K σ κ _ _ _ r0 r1 l s T I pos ξ col β h
  rcases h with ⟨k, hk⟩ | ⟨k, k', hne, hk, hk', -, h | h⟩ | ⟨k, hk, h | h⟩
  · refine hits_row s T I pos ξ col {k} (ξ k) (fun k' hk' => by rw [Finset.mem_singleton.mp hk']) β ?_
    rw [Finset.sum_singleton]
    omega
  · refine hits_row s T I pos ξ col {k, k'} (ξ k) (fun j hj => ?_) β ?_
    · rcases Finset.mem_insert.mp hj with rfl | hj
      · rfl
      · rw [Finset.mem_singleton.mp hj, h]
    · rw [Finset.sum_pair hne]
      omega
  · refine hits_col s T I pos ξ col {k, k'} {col k} (fun j hj _ => ?_) β ?_
    · rcases Finset.mem_insert.mp hj with rfl | hj
      · exact Finset.mem_singleton_self _
      · rw [Finset.mem_singleton.mp hj, h]
        exact Finset.mem_singleton_self _
    · rw [Finset.sum_pair hne]
      have : ((univ.image I) ∩ {col k}).card ≤ 1 :=
        (Finset.card_le_card Finset.inter_subset_right).trans (by simp)
      omega
  · refine hits_col s T I pos ξ col {k} ∅ (fun j hj hp => ?_) β ?_
    · rw [Finset.mem_singleton.mp hj] at hp
      exact absurd hp h
    · rw [Finset.sum_singleton, Finset.inter_empty, Finset.card_empty]
      omega
  · refine hits_col s T I pos ξ col {k} {col k} (fun j hj _ => ?_) β ?_
    · rw [Finset.mem_singleton.mp hj]
      exact Finset.mem_singleton_self _
    · have : (univ.image I) ∩ {col k} = ∅ := by
        ext y
        simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_univ, true_and,
          Finset.mem_singleton, Finset.notMem_empty, iff_false]
        rintro ⟨⟨c, rfl⟩, hc⟩
        exact h ⟨c, hc⟩
      rw [Finset.sum_singleton, this, Finset.card_empty]
      omega
end Formalism.InvariantFactorPaths.G7
