-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.markov_inequality_vector
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:04:56.801897+00:00
-- url     : https://prove2.me/submissions/482d91f0-9b4e-4202-8167-e6117aa12915

import Definitions.Def_Formalism_HermitianCurvature_StatementE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Markov
import Theorems.Thm_Formalism_FourierDecayAlt_P_markov_inequality
import Theorems.Thm_Formalism_FourierDecayAlt_P_markovVector_of

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
theorem _root_.solution : Formalism.FourierDecayAlt.E.MarkovVector := markovVector_of markov_inequality
end Formalism.FourierDecayAlt.P
