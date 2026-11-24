-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.Top.stripsMem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:08:01.595514+00:00
-- url     : https://prove2.me/submissions/788b442d-17fe-4a65-9209-0ddbc78a2163

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_AntitoneOfMemGtBox
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_Branch
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_NormIndexCountBound
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_FinalP
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_strips_mem


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
theorem _root_.solution : StripsMem := by
  first
  | exact stripsMem_proof
  | exact P.stripsMem_proof
  | exact strips_mem
  | exact P.strips_mem
  | exact Formalism.InvariantFactorPaths.GelfandTsetlinBases.P.stripsMem_proof
  | exact Formalism.InvariantFactorPaths.GelfandTsetlinBases.P.strips_mem
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.Top
