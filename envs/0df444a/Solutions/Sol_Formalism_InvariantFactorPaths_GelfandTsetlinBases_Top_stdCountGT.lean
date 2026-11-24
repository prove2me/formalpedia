-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.Top.stdCountGT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:14:47.726003+00:00
-- url     : https://prove2.me/submissions/41343fef-b64d-450c-bbf8-430e717ae256

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_AntitoneOfMemGtBox
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_Branch
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_NormIndexCountBound
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_FinalP
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_standard_count_gt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases Formalism.InvariantFactorPaths.GelfandTsetlinBases.Top
open Formalism.InvariantFactorPaths.GelfandTsetlinBases
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.Top
theorem _root_.solution : StdCountGT := by
  first
  | exact stdCountGT_proof
  | exact P.stdCountGT_proof
  | exact standard_count_gt
  | exact P.standard_count_gt
  | exact Formalism.InvariantFactorPaths.GelfandTsetlinBases.P.stdCountGT_proof
  | exact Formalism.InvariantFactorPaths.GelfandTsetlinBases.P.standard_count_gt
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.Top
