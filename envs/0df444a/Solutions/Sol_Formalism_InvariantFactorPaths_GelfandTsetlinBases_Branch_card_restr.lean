-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch.card_restr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:13.640461+00:00
-- url     : https://prove2.me/submissions/99c5157d-0d8d-4163-a705-93dd9bf2fb21

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementP
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LinearIndependentOfLead
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_Branch

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
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch
theorem _root_.solution {n : ℕ} (A : Finset (Fin (n + 1))) : (restr A).card = cnt A n := by
  rw [← cnt_restr A le_rfl]
  exact (cnt_of_le _ le_rfl).symm
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch
