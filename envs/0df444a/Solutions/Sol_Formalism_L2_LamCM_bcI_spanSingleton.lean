-- Prove2me | solution 1 for Formalism.L2.LamCM.bcI_spanSingleton
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:42:42.131954+00:00
-- url     : https://prove2.me/submissions/d738a9fb-c254-4ac3-9da1-ea2bd449304f

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementP
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CmNumbersLink
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_CountSpanSingletonAlgebraMapEqZero
import Theorems.Thm_Formalism_L2_LamCM_locMap_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
variable {K K1 : Type} [Field K] [NumberField K] [Field K1] [NumberField K1] [Algebra K K1]
namespace Formalism.L2.LamCM
theorem _root_.solution (x : K) :
    bcI (K1 := K1) (FractionalIdeal.spanSingleton (𝓞 K)⁰ x) =
      FractionalIdeal.spanSingleton (𝓞 K1)⁰ (algebraMap K K1 x) := by
  rw [bcI, FractionalIdeal.extended_spanSingleton, locMap_eq]
end Formalism.L2.LamCM
