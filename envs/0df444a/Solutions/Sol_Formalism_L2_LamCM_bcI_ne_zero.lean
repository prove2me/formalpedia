-- Prove2me | solution 1 for Formalism.L2.LamCM.bcI_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:31:56.176513+00:00
-- url     : https://prove2.me/submissions/f9ec83bb-1097-4693-affa-a39d3ac99519

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
theorem _root_.solution {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) : bcI (K1 := K1) I ≠ 0 := FractionalIdeal.extended_ne_zero _ _ (Formalism.L2.LamCM.algebraMap_int_injective (K := K) (K1 := K1)) hI
  (fun h => (mem_nonZeroDivisors_iff_ne_zero.mp h) rfl)
end Formalism.L2.LamCM
