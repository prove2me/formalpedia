-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.pos_I
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:43:45.296819+00:00
-- url     : https://prove2.me/submissions/0575a78a-99ee-47f6-9a04-8c02993d03de

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_N0LeNs
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_tailPos_mono
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_n0_le_Ns
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_stage_le
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_stLen_le
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_latestV_succ
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_latestV_frame
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_actV_true
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
theorem _root_.solution (hW : D.Wf) (hP : D.IsPATH mu) (i u : ℕ) (hN : i < D.Ns) (ha : actV D (i + 1) = false) :
    tailPos (D.stLen (i + 1)) (stage mu (i + 1)) u ≤ tailPos (D.stLen i) (stage mu i) u ∧
      D.SPos u (i + 1) = D.SPos u i := by
  by_cases hi : i + 1 ≤ D.n0
  · have hv : D.vec (i + 1) = false := by
      by_contra h
      have h' : actV D (i + 1) = true := actV_true.2 ⟨hi, by simpa using h⟩
      simp [h'] at ha
    have hS := hP.2.2.2.1 (i + 1) (by omega) (hi.trans (n0_le_Ns D)) hv
    simp only [Nat.add_sub_cancel] at hS
    refine ⟨?_, ?_⟩
    · rw [stLen_le _ hi, stLen_le _ (by omega), stage_le _ hi, stage_le _ (by omega)]
      exact tailPos_mono hS.1 u
    · unfold Letters.SPos
      rw [latestV_succ i hi, if_neg (by simp [hv])]
  · refine ⟨(frame_step hW hP i u hN (by omega)).1, ?_⟩
    unfold Letters.SPos
    rw [latestV_frame (i + 1) i (by omega) (by omega)]
end Formalism.InvariantFactorPaths.BranchingDimensions
