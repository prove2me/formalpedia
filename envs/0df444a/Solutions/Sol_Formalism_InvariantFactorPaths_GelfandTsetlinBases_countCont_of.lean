-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.countCont_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:01:32.220513+00:00
-- url     : https://prove2.me/submissions/b2d099f1-d249-4912-b160-f80a83b088d6

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementP
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_NormIndexCountBound
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Count_norm_index_count_bound

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
theorem _root_.solution : StripsMem → GTPieri → StdCountGT → CountCont := by
  intro hS hP hC n i N isVec B μ₀ hiN hμ
  exact Count.norm_index_count_bound hS hP hC n N isVec B (N - i) i (by omega) μ₀ hμ
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
