-- Prove2me | solution 1 for Formalism.L2.Pj.embK_coe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:21:00.238841+00:00
-- url     : https://prove2.me/submissions/39ad406e-f498-4b36-bfe7-b7c4abff1814

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_EmbKCoe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {l : Level H} (c : Coeff l)
namespace Formalism.L2.Pj
theorem _root_.solution (τ : E →+* ℂ) (a : 𝓞 E) : ((embK c τ a : c.F) : ℂ) = τ (a : E) := rfl
end Formalism.L2.Pj
