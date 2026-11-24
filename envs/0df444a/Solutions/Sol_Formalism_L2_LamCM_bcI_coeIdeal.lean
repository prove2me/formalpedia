-- Prove2me | solution 1 for Formalism.L2.LamCM.bcI_coeIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:32:57.487128+00:00
-- url     : https://prove2.me/submissions/2d65b762-7e09-417b-9241-a229d2108d2f

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
theorem _root_.solution (J : Ideal (𝓞 K)) :
    bcI (K1 := K1) (J : FractionalIdeal (𝓞 K)⁰ K) = ((J.map (algebraMap (𝓞 K) (𝓞 K1)) : Ideal (𝓞 K1)) :
      FractionalIdeal (𝓞 K1)⁰ K1) := FractionalIdeal.extended_coeIdeal_eq_map _ _ _
end Formalism.L2.LamCM
