-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.cov_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:05:37.803468+00:00
-- url     : https://prove2.me/submissions/ac1674fc-5803-4694-8049-70b9e88cf6cd

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
theorem _root_.solution (hP : D.IsPATH mu) (i : ℕ) (hi : i + 1 ≤ D.n0) (hv : D.vec (i + 1) = false) :
    HStrip D.k (ent mu (i + 1)) (ent mu i) ∧
      wsize D.k (ent mu i) - wsize D.k (ent mu (i + 1)) = D.B (i + 1) := by
  obtain ⟨-, -, -, h4, -, h6, -⟩ := hP
  have e : i + 1 - 1 = i := by omega
  have ha := h4 (i + 1) (by omega) (hi.trans (n0_le_Ns D)) hv
  have hb := h6 (i + 1) (by omega) hi hv
  rw [e] at ha hb
  exact ⟨ha, hb⟩
end Formalism.InvariantFactorPaths.BranchingDimensions
