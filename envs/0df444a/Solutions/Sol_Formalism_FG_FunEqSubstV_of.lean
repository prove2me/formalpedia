-- Prove2me | solution 1 for Formalism.FG.FunEqSubstV_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:57:46.133966+00:00
-- url     : https://prove2.me/submissions/6ab62cb6-535b-4202-8e4b-82ca111d9b9e

import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_IntegralSubstVector
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_NormSigmaLeOne
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CoeffV
import Definitions.Def_Lemmata_MultivariateIntegrals_IntegralMv
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FunctionalEquationSubstVector
import Theorems.Thm_Formalism_FG_KeyVAux_main
import Theorems.Thm_Formalism_FG_CoefficientBoundsFormalGroupWitt_main
import Theorems.Thm_Formalism_LT_FrobP_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v w
namespace Formalism.FG
theorem _root_.solution (hC : Formalism.FG.CoeffBoundV.{u, v, v}) :
    Formalism.FG.FunEqSubstV.{u, v, w} :=
  Formalism.FG.KeyVAux.main hC
end Formalism.FG
