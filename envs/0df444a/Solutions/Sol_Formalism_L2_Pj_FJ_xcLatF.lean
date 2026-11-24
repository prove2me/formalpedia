-- Prove2me | solution 1 for Formalism.L2.Pj.FJ.xcLatF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:33:20.636046+00:00
-- url     : https://prove2.me/submissions/06571d27-7ccd-4d1a-aa74-89f260b4a4c0

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntegrableOnIntegrand
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LocalSituation
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SpanRatSmulMem
import Theorems.Thm_Formalism_L2_Pj_FJ_xcFD_lat

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
theorem _root_.solution {Comp : Type} (X : Comp → Data E r) (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
    (h𝔄 : 𝔄 ≠ 0) : XcLatF X 𝔄 ρ :=
  fun cu => xcFD_lat 𝔄 h𝔄 cu.2
end Formalism.L2.Pj.FJ
