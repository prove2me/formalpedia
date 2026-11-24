-- Prove2me | solution 1 for Formalism.L2.Pj.FJ.xcFD_restrict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:23:11.128526+00:00
-- url     : https://prove2.me/submissions/b21dab1e-c24b-444c-9543-58375e9df816

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntegrableOnIntegrand
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LocalSituation
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SpanRatSmulMem
import Theorems.Thm_Formalism_L2_Pj_FJ_dualZE_eq
import Theorems.Thm_Formalism_L2_Pj_FJ_xcFD_coe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open NumberField ReciprocityTheory.ChartRestriction.G.FD
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.FJ
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}
namespace Formalism.L2.Pj.FJ
theorem _root_.solution (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) {X : Data E r} (cu : CuspFD X ρ) :
    (XcFD 𝔄 cu).restrictScalars ℤ = (trBE ρ).dualSubmodule ((crdI 𝔄 cu).restrictScalars ℤ) := by
  apply SetLike.coe_injective
  rw [Submodule.coe_restrictScalars, xcFD_coe, dualZE_eq]
end Formalism.L2.Pj.FJ
