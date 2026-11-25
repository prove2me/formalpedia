-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.Top.weylP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:00:44.877901+00:00
-- url     : https://prove2.me/submissions/41c3fe06-bf86-46c8-90a3-66393137d8ef

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_FinalP
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_WeylInt
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_ZpClosedToAddSubgroup
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_CompEqZeroOfNotDle
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_DischargeHeightBound
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_Top_weylInt
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_lattice_basis_polynomial
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_weylP_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW Formalism.InvariantFactorPaths.PW.Top
namespace Formalism.InvariantFactorPaths.PW.Top
theorem _root_.solution : WeylP := weylP_of weylInt lattice_basis_polynomial
end Formalism.InvariantFactorPaths.PW.Top
