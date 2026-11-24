-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.neg_I
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:43:44.339803+00:00
-- url     : https://prove2.me/submissions/30c28147-14a5-42c4-a637-a062285b65d0

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_N0LeNs
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_tailNeg_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_tailPos_mono
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_n0_le_Ns
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_stage_le
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_stLen_le
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_latestC_succ
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_latestC_frame
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_actC_true
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_frame_step

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
theorem _root_.solution (hW : D.Wf) (hP : D.IsPATH mu) (i u : ℕ) (hN : i < D.Ns) (ha : actC D (i + 1) = false) :
    tailNeg (D.stLen (i + 1)) (stage mu (i + 1)) u ≤ tailNeg (D.stLen i) (stage mu i) u ∧
      D.SNeg u (i + 1) = D.SNeg u i := by
  by_cases hi : i + 1 ≤ D.n0
  · have hv : D.vec (i + 1) = true := by
      by_contra h
      have h' : actC D (i + 1) = true := actC_true.2 ⟨hi, by simpa using h⟩
      simp [h'] at ha
    have hS := hP.2.2.1 (i + 1) (by omega) (hi.trans (n0_le_Ns D)) hv
    simp only [Nat.add_sub_cancel] at hS
    refine ⟨?_, ?_⟩
    · rw [stLen_le _ hi, stLen_le _ (by omega), stage_le _ hi, stage_le _ (by omega), tailNeg_eq, tailNeg_eq]
      exact tailPos_mono (fun m hm => by unfold revW; exact neg_le_neg (hS.1 _ (by omega))) u
    · unfold Letters.SNeg
      rw [latestC_succ i hi, if_neg (by simp [hv])]
  · refine ⟨(frame_step hW hP i u hN (by omega)).2, ?_⟩
    unfold Letters.SNeg
    rw [latestC_frame (i + 1) i (by omega) (by omega)]
end Formalism.InvariantFactorPaths.BranchingDimensions
