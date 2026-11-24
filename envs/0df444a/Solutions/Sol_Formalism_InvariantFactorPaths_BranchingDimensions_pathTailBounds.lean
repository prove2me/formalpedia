-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.pathTailBounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:50:26.398814+00:00
-- url     : https://prove2.me/submissions/4cb4a24c-7993-46b6-a09c-80748aa199c5

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_N0LeNs
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_tailNeg_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_abs_bound
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_deficit_persists_of_active_inactive_recursion
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_n0_le_Ns
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_stage_le
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_latestV_frame
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_latestC_frame
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_tailPos_of_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_card_actV
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_card_actC
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_pos_A
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_pos_active_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_pos_I
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_neg_A
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_neg_active_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_neg_I

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
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.BranchingDimensions
open Letters
variable {D : Letters} {mu : D.Stages}
namespace Formalism.InvariantFactorPaths.BranchingDimensions
theorem _root_.solution : PathTailBounds := by
  intro D mu hW hP
  have hk0 : ∀ u, tailPos (D.stLen 0) (stage mu 0) u = 0 := by
    intro u
    apply tailPos_of_zero
    intro m
    rw [stage_le 0 (Nat.zero_le _)]
    exact hP.1 m
  have hk0' : ∀ u, tailNeg (D.stLen 0) (stage mu 0) u = 0 := by
    intro u
    rw [tailNeg_eq]
    apply tailPos_of_zero
    intro m
    simp [revW, stage_le 0 (Nat.zero_le _), hP.1]
  have bP := abs_bound D.Ns (fun i u => tailPos (D.stLen i) (stage mu i) u) (fun u i => D.SPos u i) (actV D)
    (fun u => by
      show tailPos (D.stLen 0) (stage mu 0) u ≤ (D.SPos u 0 : ℤ)
      rw [hk0]
      exact Nat.cast_nonneg _)
    (fun i u _ ha => pos_A hP i u ha) (fun i _ ha => pos_active_zero hP i ha) (fun i u hi ha => pos_I hW hP i u hi ha)
  have bN := abs_bound D.Ns (fun i u => tailNeg (D.stLen i) (stage mu i) u) (fun u i => D.SNeg u i) (actC D)
    (fun u => by
      show tailNeg (D.stLen 0) (stage mu 0) u ≤ (D.SNeg u 0 : ℤ)
      rw [hk0']
      exact Nat.cast_nonneg _)
    (fun i u _ ha => neg_A hP i u ha) (fun i _ ha => neg_active_zero hP i ha) (fun i u hi ha => neg_I hW hP i u hi ha)
  have hsP : ∀ v, D.SPos v D.Ns = D.SPos v D.n0 := fun v => by
    unfold Letters.SPos
    rw [latestV_frame D.Ns D.n0 (n0_le_Ns D) le_rfl]
  have hsN : ∀ v, D.SNeg v D.Ns = D.SNeg v D.n0 := fun v => by
    unfold Letters.SNeg
    rw [latestC_frame D.Ns D.n0 (n0_le_Ns D) le_rfl]
  refine ⟨fun i u hi => ⟨bP i hi u, bN i hi u⟩, fun i₀ u X hi₀ _ h => ?_, fun i₀ u X hi₀ _ h => ?_⟩
  · have h1 := deficit_persists_of_active_inactive_recursion D.Ns (fun i u => tailPos (D.stLen i) (stage mu i) u) (fun u i => D.SPos u i) (actV D)
      (fun i u _ ha => pos_A hP i u ha) (fun i u hi ha => pos_I hW hP i u hi ha) i₀ u X h D.Ns hi₀ le_rfl
    beta_reduce at h1
    rw [card_actV, hsP] at h1
    exact h1
  · have h1 := deficit_persists_of_active_inactive_recursion D.Ns (fun i u => tailNeg (D.stLen i) (stage mu i) u) (fun u i => D.SNeg u i) (actC D)
      (fun i u _ ha => neg_A hP i u ha) (fun i u hi ha => neg_I hW hP i u hi ha) i₀ u X h D.Ns hi₀ le_rfl
    beta_reduce at h1
    rw [card_actC, hsN] at h1
    exact h1
end Formalism.InvariantFactorPaths.BranchingDimensions
