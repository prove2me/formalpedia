-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.pos_active_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:00:20.342818+00:00
-- url     : https://prove2.me/submissions/88baac97-b9bf-413a-9faa-e707017569f8

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_N0LeNs
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_HStrip_tailPos_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_n0_le_Ns
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_stage_le
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_stLen_le
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_latestV_succ
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_actV_true

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
theorem _root_.solution (hP : D.IsPATH mu) (i : ℕ) (ha : actV D (i + 1) = true) :
    tailPos (D.stLen (i + 1)) (stage mu (i + 1)) 0 - tailPos (D.stLen i) (stage mu i) 0 ≤
      (D.SPos 0 (i + 1) : ℤ) - D.SPos 0 i := by
  obtain ⟨hi, hv⟩ := actV_true.1 ha
  have hS := hP.2.2.1 (i + 1) (by omega) (hi.trans (n0_le_Ns D)) hv
  have hW := hP.2.2.2.2.1 (i + 1) (by omega) hi hv
  simp only [Nat.add_sub_cancel] at hS hW
  rw [stLen_le _ hi, stLen_le _ (by omega), stage_le _ hi, stage_le _ (by omega)]
  unfold Letters.SPos
  rw [latestV_succ i hi, if_pos hv, List.drop_zero, List.drop_zero, List.sum_cons]
  have h1 := hS.tailPos_zero
  push_cast
  linarith
end Formalism.InvariantFactorPaths.BranchingDimensions
