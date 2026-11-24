-- Prove2me | solution 1 for Formalism.L2.LamCM.A2.detIdeal_free
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:12:50.488633+00:00
-- url     : https://prove2.me/submissions/14161f7b-ea0c-43e4-9ade-a5aa83878a63

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementA
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ProdMulLeDetIdeal
import Theorems.Thm_Formalism_L2_LamCM_A2_detSub_isFractional
import Theorems.Thm_Formalism_L2_LamCM_A2_detIdeal_coe
import Theorems.Thm_Formalism_L2_LamCM_A2_detSub_free

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
open scoped nonZeroDivisors ComplexOrder
open Formalism.L2.LamCM.A2
variable {K : Type} [Field K] [NumberField K]
namespace Formalism.L2.LamCM.A2
theorem _root_.solution {m : ℕ} (L : MLat K m) (b : Fin m → Fin m → K) (hL : L.Good)
    (hb : L.M = Submodule.span (𝓞 K) (Set.range b)) :
    L.detIdeal = FractionalIdeal.spanSingleton (𝓞 K)⁰ (Matrix.of b).det := by
  apply FractionalIdeal.coeToSubmodule_injective
  show (L.detIdeal : Submodule (𝓞 K) K) = (FractionalIdeal.spanSingleton (𝓞 K)⁰ (Matrix.of b).det : Submodule (𝓞 K) K)
  rw [detIdeal_coe L (detSub_isFractional L hL.1), FractionalIdeal.coe_spanSingleton, detSub_free L b hb]
end Formalism.L2.LamCM.A2
