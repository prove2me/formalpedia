-- Prove2me | solution 1 for Formalism.L2.Pj.FJ.xcFD_coe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:47:52.084054+00:00
-- url     : https://prove2.me/submissions/4beb520a-41d7-4a62-ad90-5fa19ebf5282

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntegrableOnIntegrand
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LocalSituation
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SpanRatSmulMem

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
    (XcFD 𝔄 cu : Set (Fin ρ → E)) = dualZE (crdI 𝔄 cu) := by
  have h : XcFD 𝔄 cu = dualZSubE (crdI 𝔄 cu) := Submodule.span_eq (dualZSubE (crdI 𝔄 cu))
  rw [h]; rfl
end Formalism.L2.Pj.FJ
