-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.card_actC
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:00:49.159716+00:00
-- url     : https://prove2.me/submissions/f8b17e2f-ce47-41e8-bdf0-d41fdaa85426

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_N0LeNs
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_n0_le_Ns
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
theorem _root_.solution (i₀ : ℕ) : ((Icc (i₀ + 1) D.Ns).filter fun l => actC D l = true).card =
    ((Icc (i₀ + 1) D.n0).filter fun l => D.vec l = false).card := by
  have hn := n0_le_Ns D
  congr 1
  ext l
  simp only [Finset.mem_filter, Finset.mem_Icc, actC_true]
  constructor
  · rintro ⟨⟨h1, _⟩, h3, h4⟩
    exact ⟨⟨h1, h3⟩, h4⟩
  · rintro ⟨⟨h1, h2⟩, h4⟩
    exact ⟨⟨h1, le_trans h2 hn⟩, h2, h4⟩
end Formalism.InvariantFactorPaths.BranchingDimensions
