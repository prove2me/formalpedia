-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.rule_B_derivatives
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:50:16.460438+00:00
-- url     : https://prove2.me/submissions/8136a121-6d32-43f8-9534-ad2c265cf5fa

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiBoundPartsOfRadicalParametrisation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MajorantEstimate
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DerivativeRulesA1
import Theorems.Thm_Formalism_FourierDecayAlt_P_SmoothnessOrderArithmetic_ruleB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C2.RuleB := SmoothnessOrderArithmetic.ruleB
end Formalism.FourierDecayAlt.P
