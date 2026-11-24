-- Prove2me | solution 1 for Formalism.L2.Pj.CompSplitPfD.cspD_comp_disj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:05:43.218233+00:00
-- url     : https://prove2.me/submissions/755ed35d-282a-4e95-a97f-94340d553ea5

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsGenFrGenFr
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompFin
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompSplitPfC
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompSplitPfD
import Theorems.Thm_Formalism_L2_Pj_CompSplitPfD_cspD_disj
import Theorems.Thm_Formalism_L2_Pj_CompSplitPfD_cspD_local

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.CompSplitPfD
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Topology
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
namespace Formalism.L2.Pj.CompSplitPfD
theorem _root_.solution (Xo : Moduli Dw l) (c : Coeff l) (Z Z' : Comp Xo c) (hne : Z ≠ Z') :
    Disjoint (Z : Set (Xo.XF c)) Z' := cspD_disj (cspD_local Xo c) Z Z' Z.2 Z'.2 (fun h => hne (Subtype.ext h))
end Formalism.L2.Pj.CompSplitPfD
