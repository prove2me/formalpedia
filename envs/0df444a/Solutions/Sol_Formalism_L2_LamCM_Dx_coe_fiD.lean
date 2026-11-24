-- Prove2me | solution 1 for Formalism.L2.LamCM.Dx.coe_fiD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:51:30.267025+00:00
-- url     : https://prove2.me/submissions/43198fd2-e0e0-49c8-899a-c25092eb4c19

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CmNumbersLink
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_AbsNormEqRelIndexMul
import Theorems.Thm_Formalism_L2_LamCM_Dx_dS_isFractional
import Theorems.Thm_Formalism_L2_LamCM_A2_detIdeal_coe


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
open Formalism.L2.LamCM.Dx
variable {K : Type} [Field K] [NumberField K]
namespace Formalism.L2.LamCM.Dx
theorem _root_.solution {n : ℕ} (M : Submodule (𝓞 K) (Fin n → K)) (hM : Sand M) : (fiD M : Submodule (𝓞 K) K) = dS M :=
  A2.detIdeal_coe _ (dS_isFractional M hM)
end Formalism.L2.LamCM.Dx
