-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.neg_A
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:43:42.906261+00:00
-- url     : https://prove2.me/submissions/10299337-fb8f-4bdc-836b-f9a13f4216ee

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_N0LeNs
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_tailNeg_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_HStrip_rev
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_Interl_rev
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_HStrip_tailPos_shift
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_n0_le_Ns
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_stage_le
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_stLen_le
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_latestC_succ
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_actC_true

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
theorem _root_.solution (hP : D.IsPATH mu) (i u : ℕ) (ha : actC D (i + 1) = true) :
    tailNeg (D.stLen (i + 1)) (stage mu (i + 1)) (u + 1) ≤ tailNeg (D.stLen i) (stage mu i) u ∧
      D.SNeg (u + 1) (i + 1) = D.SNeg u i := by
  obtain ⟨hi, hv⟩ := actC_true.1 ha
  have hS := hP.2.2.2.1 (i + 1) (by omega) (hi.trans (n0_le_Ns D)) hv
  simp only [Nat.add_sub_cancel] at hS
  refine ⟨?_, ?_⟩
  · rw [stLen_le _ hi, stLen_le _ (by omega), stage_le _ hi, stage_le _ (by omega), tailNeg_eq, tailNeg_eq]
    exact hS.rev.tailPos_shift u
  · unfold Letters.SNeg
    rw [latestC_succ i hi, if_pos (by simp [hv]), List.drop_succ_cons]
end Formalism.InvariantFactorPaths.BranchingDimensions
