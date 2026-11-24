-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.frame_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:32:31.775031+00:00
-- url     : https://prove2.me/submissions/28cd1599-b2aa-4639-b562-cd6e32d8d99d

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_N0LeNs
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_tailNeg_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_HStrip_rev
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_Interl_rev
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_HStrip_tailPos_le
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_Interl_tailPos_le
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_Ns_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_r_lt_k
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_stLen_add
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_interl_of_path

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
theorem _root_.solution (hW : D.Wf) (hP : D.IsPATH mu) (i u : ℕ) (hi : i < D.Ns) (hn : D.n0 ≤ i) :
    tailPos (D.stLen (i + 1)) (stage mu (i + 1)) u ≤ tailPos (D.stLen i) (stage mu i) u ∧
    tailNeg (D.stLen (i + 1)) (stage mu (i + 1)) u ≤ tailNeg (D.stLen i) (stage mu i) u := by
  obtain ⟨j, rfl⟩ : ∃ j, i = D.n0 + j := ⟨i - D.n0, by omega⟩
  have hNs := Ns_eq hW
  have hj : j < D.r := by omega
  have hI := interl_of_path hW hP j hj
  have hl1 : D.stLen (D.n0 + j + 1) = D.k - (j + 1) := by rw [add_assoc, stLen_add]
  have hl0 : D.stLen (D.n0 + j) = D.k - j := stLen_add j
  have hkj : D.k - j = D.k - (j + 1) + 1 := by
    have := r_lt_k hW
    omega
  rw [hl1, hl0, hkj, show D.n0 + j + 1 = D.n0 + (j + 1) by ring]
  refine ⟨hI.tailPos_le u, ?_⟩
  rw [tailNeg_eq, tailNeg_eq]
  exact hI.rev.tailPos_le u
end Formalism.InvariantFactorPaths.BranchingDimensions
