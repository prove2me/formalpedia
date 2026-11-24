-- Prove2me | solution 1 for Formalism.L2.LamCM.bcI_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:31:55.146322+00:00
-- url     : https://prove2.me/submissions/9ec7be96-67f3-43f5-9ac8-11eb875fb6a1

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementP
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CmNumbersLink
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_CountSpanSingletonAlgebraMapEqZero

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
theorem _root_.solution (I J : FractionalIdeal (𝓞 K)⁰ K) : bcI (K1 := K1) (I * J) = bcI I * bcI J := FractionalIdeal.extended_mul ..
end Formalism.L2.LamCM
