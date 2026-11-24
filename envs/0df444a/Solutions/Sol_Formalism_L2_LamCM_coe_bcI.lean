-- Prove2me | solution 1 for Formalism.L2.LamCM.coe_bcI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:42:35.21086+00:00
-- url     : https://prove2.me/submissions/f096edd3-fb4c-461f-badc-17896970813a

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
theorem _root_.solution (I : FractionalIdeal (𝓞 K)⁰ K) :
    ((bcI (K1 := K1) I : FractionalIdeal (𝓞 K1)⁰ K1) : Submodule (𝓞 K1) K1) =
      Submodule.span (𝓞 K1) (algebraMap K K1 '' {x | x ∈ I}) := by
  rw [bcI, FractionalIdeal.coe_extended_eq_span, locMap_eq]
  rfl
end Formalism.L2.LamCM
