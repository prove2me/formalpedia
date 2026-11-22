-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.HStrip.rev
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:22:33.122637+00:00
-- url     : https://prove2.me/submissions/349323ee-7396-404a-a5a8-ff59e1998085

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_N0LeNs

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
namespace Formalism.InvariantFactorPaths.BranchingDimensions
namespace HStrip
theorem _root_.solution {n : ℕ} {a b : ℕ → ℤ} (h : HStrip n a b) : HStrip n (revW n b) (revW n a) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun m hm => ?_, fun m hm => ?_⟩
  · simp only [revW]
    exact neg_le_neg (h1 _ (by omega))
  · simp only [revW]
    have h3 := h2 (n - 1 - (m + 1)) (by omega)
    have e : n - 1 - (m + 1) + 1 = n - 1 - m := by omega
    rw [e] at h3
    exact neg_le_neg h3
end HStrip
end Formalism.InvariantFactorPaths.BranchingDimensions
