-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.corollary_a_of_proposition_a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:18:40.818799+00:00
-- url     : https://prove2.me/submissions/d7f14b60-e70f-4aea-837f-2fb4b77ba7ae

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz2_corA_of_propA
import Theorems.Thm_Formalism_FourierDecayAlt_P_massRatioFormula


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
theorem _root_.solution : Formalism.FourierDecayAlt.Sz.CorA := Sz2.corA_of_propA massRatioFormula
end Formalism.FourierDecayAlt.P
