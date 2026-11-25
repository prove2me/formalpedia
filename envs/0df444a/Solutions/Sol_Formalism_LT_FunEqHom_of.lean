-- Prove2me | solution 1 for Formalism.LT.FunEqHom_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:01:46.907044+00:00
-- url     : https://prove2.me/submissions/c100e582-0ae3-4dd1-a1ad-4aceb5f1283f

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MapSubtypeInjective
import Theorems.Thm_P2M_Formalism_LT_Asm_FunEqHom_of__1ee5dca2153b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
universe u
open Formalism Formalism.LT
namespace Formalism.LT
theorem _root_.solution (h1 : Formalism.LT.SolveExists.{u, 0}) (h2 : Formalism.LT.InvIntegralOfClass.{u, 0})
    (h3 : Formalism.LT.FunEqLowCoeff.{u, 0}) (hk : Formalism.G.FunEqSubst.{u, 0}) : Formalism.G.FunEqHom.{u} :=
  Formalism.LT.Asm.FunEqHom_of' h1 h2 h3 hk
end Formalism.LT
