-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.duality_minus
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:23.613921+00:00
-- url     : https://prove2.me/submissions/c37a87d0-e485-4159-894b-2078f2513a29

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondEmbedMulFirstEmbedApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteOfEntries
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_dualMinus_of
import Theorems.Thm_Formalism_FourierDecayAlt_P_exchange_relation_plus


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.Wd.DualMinus := Wd9.dualMinus_of exchange_relation_plus
end Formalism.FourierDecayAlt.P
