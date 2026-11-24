-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.Top.gtPieri
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:59:09.505503+00:00
-- url     : https://prove2.me/submissions/c3662a0e-4a72-451c-9975-e9d0db1377ae

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_AntitoneOfMemGtBox
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_Branch
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_NormIndexCountBound
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_FinalP
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_gelfand_tsetlin_pieri


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
theorem _root_.solution : GTPieri := by
  first
  | exact gtPieri_proof
  | exact P.gtPieri_proof
  | exact gelfand_tsetlin_pieri
  | exact P.gelfand_tsetlin_pieri
  | exact Formalism.InvariantFactorPaths.GelfandTsetlinBases.P.gtPieri_proof
  | exact Formalism.InvariantFactorPaths.GelfandTsetlinBases.P.gelfand_tsetlin_pieri
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.Top
