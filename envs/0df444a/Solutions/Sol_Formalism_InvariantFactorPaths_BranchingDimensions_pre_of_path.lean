-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.pre_of_path
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:48:42.974518+00:00
-- url     : https://prove2.me/submissions/3ad9666c-9954-48c9-8b57-74607b539b17

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_N0LeNs
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_n0_le_Ns

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
theorem _root_.solution (h : D.IsPATH mu) : D.IsPre mu := by
  obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := h
  exact ⟨h1, fun i hi => h2 i (hi.trans (n0_le_Ns D)),
    fun i hi1 hi2 hv => h3 i hi1 (hi2.trans (n0_le_Ns D)) hv,
    fun i hi1 hi2 hv => h4 i hi1 (hi2.trans (n0_le_Ns D)) hv, h5, h6⟩
end Formalism.InvariantFactorPaths.BranchingDimensions
