-- Prove2me | solution 1 for Formalism.L2.Pj.CompSplitPfD.cspD_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:14:44.37006+00:00
-- url     : https://prove2.me/submissions/4d52a9b7-7c47-403d-b3f3-441ea31aa23b

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsGenFrGenFr
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompFin
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompSplitPfC
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompSplitPfD

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
theorem _root_.solution (Xo : Moduli Dw l) (c : Coeff l) :
    Smooth (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) := by
  first
    | (haveI := Xo.smooth; exact MorphismProperty.pullback_snd _ _ inferInstance)
    | (haveI := Xo.smooth; infer_instance)
    | (haveI := Xo.smooth; haveI : Smooth Xo.s := SmoothOfRelativeDimension.smooth Dw.dim Xo.s; infer_instance)
end Formalism.L2.Pj.CompSplitPfD
