-- Prove2me | solution 1 for Formalism.L2.Pj.kapTrdeg_pf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:10:06.932404+00:00
-- url     : https://prove2.me/submissions/e5c732c8-c06c-415e-86fc-f83619775d24

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FnTrdegOf
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_KapTrdegPfB
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_KapTrdegPf
import Theorems.Thm_Formalism_L2_Pj_TranscendenceDegreeLemmas_trdeg_residueField_genericPoint


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
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
namespace Formalism.L2.Pj
theorem _root_.solution (Xo : Moduli Dw l) (c : Coeff l) : KapTrdeg Xo c Dw.dim := by
  intro Z
  have h := @TranscendenceDegreeLemmas.trdeg_residueField_genericPoint c.F _ _ _ _
    (strK (Xo := Xo) (c := c)) Dw.dim _ _ Z.2 (algKap Z)
  exact h
end Formalism.L2.Pj
