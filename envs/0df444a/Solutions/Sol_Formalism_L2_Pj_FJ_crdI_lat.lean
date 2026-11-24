-- Prove2me | solution 1 for Formalism.L2.Pj.FJ.crdI_lat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:33:28.628217+00:00
-- url     : https://prove2.me/submissions/7652d69c-f10f-41c7-92ef-0ada529b1333

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntegrableOnIntegrand
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LocalSituation
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SpanRatSmulMem
import Theorems.Thm_Formalism_L2_Pj_FJ_crdI_fg
import Theorems.Thm_Formalism_L2_Pj_FJ_crdI_span

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
theorem _root_.solution (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (h𝔄 : 𝔄 ≠ 0) {X : Data E r}
    (cu : CuspFD X ρ) : Submodule.IsLattice ℚ ((crdI 𝔄 cu).restrictScalars ℤ) :=
  ⟨(crdI_fg 𝔄 cu).restrictScalars, by rw [Submodule.coe_restrictScalars]; exact crdI_span 𝔄 h𝔄 cu⟩
end Formalism.L2.Pj.FJ
