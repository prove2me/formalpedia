-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.standard_count_gt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:11:43.666395+00:00
-- url     : https://prove2.me/submissions/28990b1d-b511-4b75-962b-c9aef04f9e8b

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementP
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LinearIndependentOfLead
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_Branch
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Branch_tab_count

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
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
theorem _root_.solution : StdCountGT := by
  intro n μ hμ
  obtain ⟨hF, hN⟩ := Branch.tab_count n μ hμ
  haveI := hF
  exact ⟨Finite.of_equiv _ (Branch.stdEquiv μ).symm, (Nat.card_congr (Branch.stdEquiv μ)).trans hN⟩
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
