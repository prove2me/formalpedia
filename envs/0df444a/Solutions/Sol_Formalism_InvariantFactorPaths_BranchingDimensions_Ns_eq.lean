-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.Ns_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:27:28.267197+00:00
-- url     : https://prove2.me/submissions/404aa69b-f35f-4643-9c8a-15b980387555

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
variable {D : Letters} {mu : D.Stages}
namespace Formalism.InvariantFactorPaths.BranchingDimensions
theorem _root_.solution (hW : D.Wf) : D.Ns = D.n0 + D.r := by
  obtain ⟨_, _, h3, _⟩ := hW
  unfold Letters.n0
  omega
end Formalism.InvariantFactorPaths.BranchingDimensions
