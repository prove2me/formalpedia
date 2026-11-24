-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.nrmFacts_statement
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:02:33.230379+00:00
-- url     : https://prove2.me/submissions/2d2219ee-e4ee-4672-b888-e0b3e9a17ac7

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx3_nrmFacts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.M.NrmFacts := Mx3.nrmFacts
end Formalism.FourierDecayAlt.P
