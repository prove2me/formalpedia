-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.Interl.rev
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:22:33.303349+00:00
-- url     : https://prove2.me/submissions/f2cb70f3-926b-44a3-94ac-fd130562dede

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
namespace Interl
theorem _root_.solution {n : ℕ} {a b : ℕ → ℤ} (h : Interl n a b) : Interl n (revW n a) (revW (n + 1) b) := by
  intro l hl
  have h3 := h (n - 1 - l) (by omega)
  simp only [revW]
  have e1 : n + 1 - 1 - l = n - 1 - l + 1 := by omega
  have e2 : n + 1 - 1 - (l + 1) = n - 1 - l := by omega
  rw [e1, e2]
  exact ⟨neg_le_neg h3.2, neg_le_neg h3.1⟩
end Interl
end Formalism.InvariantFactorPaths.BranchingDimensions
