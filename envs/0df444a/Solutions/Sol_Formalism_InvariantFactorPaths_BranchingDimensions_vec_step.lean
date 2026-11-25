-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.vec_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:12:17.352287+00:00
-- url     : https://prove2.me/submissions/7d7407fc-c90b-4ef4-bbb5-32a002d3bfd9

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
theorem _root_.solution (hP : D.IsPATH mu) (i : ℕ) (hi : i + 1 ≤ D.n0) (hv : D.vec (i + 1) = true) :
    HStrip D.k (ent mu i) (ent mu (i + 1)) ∧
      wsize D.k (ent mu (i + 1)) - wsize D.k (ent mu i) = D.B (i + 1) := by
  obtain ⟨-, -, h3, -, h5, -, -⟩ := hP
  have e : i + 1 - 1 = i := by omega
  have ha := h3 (i + 1) (by omega) (hi.trans (n0_le_Ns D)) hv
  have hb := h5 (i + 1) (by omega) hi hv
  rw [e] at ha hb
  exact ⟨ha, hb⟩
end Formalism.InvariantFactorPaths.BranchingDimensions
