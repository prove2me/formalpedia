-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.WGT.extW_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:34:30.801041+00:00
-- url     : https://prove2.me/submissions/d330dd51-3859-4523-a586-57a2e3dd8ceb

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementW
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_AntitoneOfMemGtBox
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_WeylGT

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
open Formalism.InvariantFactorPaths.BranchingDimensions.WGT
open Formalism.InvariantFactorPaths.GelfandTsetlinBases (gtBox dGT stripsUp)
namespace Formalism.InvariantFactorPaths.BranchingDimensions.WGT
theorem _root_.solution {n : ℕ} (la : Fin n → ℤ) {m : ℕ} (h : m < n) : extW la m = la ⟨m, h⟩ := by
  simp [extW, h]
end Formalism.InvariantFactorPaths.BranchingDimensions.WGT
