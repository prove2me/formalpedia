-- Prove2me | solution 1 for Formalism.L2.LamCM.A2.absNorm_span_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:18:31.848062+00:00
-- url     : https://prove2.me/submissions/0e10969b-a358-4764-91f6-56e093958541

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementA
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ProdMulLeDetIdeal
import Theorems.Thm_Formalism_L2_LamCM_A2_abs_norm_eq_prod

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
theorem _root_.solution (x : K) :
    ((FractionalIdeal.absNorm (FractionalIdeal.spanSingleton (𝓞 K)⁰ x) : ℚ) : ℝ) = ∏ σ : K →+* ℂ, ‖σ x‖ := by
  rw [FractionalIdeal.absNorm_span_singleton (𝓞 K), abs_norm_eq_prod]
end Formalism.L2.LamCM.A2
