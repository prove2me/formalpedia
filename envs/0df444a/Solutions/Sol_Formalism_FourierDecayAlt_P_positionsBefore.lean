-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.positionsBefore
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:05:38.461647+00:00
-- url     : https://prove2.me/submissions/83b6da90-1c46-4559-9cd8-96fe6ef1ef13

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaFactorisation
import Theorems.Thm_Formalism_FourierDecayAlt_P_positionBefore
import Theorems.Thm_Formalism_FourierDecayAlt_P_positionProduct
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz6_positionsBefore_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.Sz Finset
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : PositionsBefore :=
  Sz6.positionsBefore_of positionBefore positionProduct
end Formalism.FourierDecayAlt.P
