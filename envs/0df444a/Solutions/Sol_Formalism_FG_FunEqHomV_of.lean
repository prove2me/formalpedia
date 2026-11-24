-- Prove2me | solution 1 for Formalism.FG.FunEqHomV_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:28:49.623632+00:00
-- url     : https://prove2.me/submissions/6d718a96-c3fc-4094-8136-4253351e4a2e

import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CoeffExpandEqZero
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CoeffV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_InvIntV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FunctionalEquationSubstVector
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FunctionalEquationHomVector
import Theorems.Thm_Formalism_FG_FunctionalEquationHom_main
import Theorems.Thm_Formalism_FG_CoefficientBoundsFormalGroupWitt_main
import Theorems.Thm_Formalism_FG_InvIntVAux_main
import Theorems.Thm_Formalism_FG_KeyVAux_main
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
open Formalism Formalism.FG
namespace Formalism.FG
theorem _root_.solution (hSol : Formalism.FG.SolveExistsV.{u, v, w}) (hInv : Formalism.FG.InvIntegralV.{u, v, w})
    (hLow : Formalism.FG.LowCoeffV.{u, v, w}) (hKey : Formalism.FG.FunEqSubstV.{u, v, w}) :
    Formalism.FG.FunEqHomV.{u, v, w} :=
  FunctionalEquationHom.main hSol hInv hLow hKey
end Formalism.FG
