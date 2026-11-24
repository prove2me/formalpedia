-- Prove2me | solution 1 for Formalism.L2.LamCM.mul_le_mul_r
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:13:32.897292+00:00
-- url     : https://prove2.me/submissions/be65adaf-44f6-4e30-8b2b-68393177aaed

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementA
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_OneLeAbsNormOfLeOne

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
variable {K : Type} [Field K] [NumberField K]
namespace Formalism.L2.LamCM
theorem _root_.solution {A B : FractionalIdeal (𝓞 K)⁰ K} (h : A ≤ B) (C : FractionalIdeal (𝓞 K)⁰ K) :
    A * C ≤ B * C :=
  mul_le_mul' h le_rfl
end Formalism.L2.LamCM
