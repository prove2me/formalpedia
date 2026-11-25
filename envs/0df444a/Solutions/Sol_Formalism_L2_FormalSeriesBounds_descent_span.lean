-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.descent_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:08:44.837479+00:00
-- url     : https://prove2.me/submissions/fb05ddd4-4122-4c9d-a166-9c0a8f6e0abb

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHaSpan
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHaLeaves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePDescSpanFinal
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_HaP_haSpanSt_of
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_HaP_rowInvUp
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_HaP_satRetr
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_descSpanSt_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution : DescSpanSt Xo c :=
  descSpanSt_of (HaP.haSpanSt_of HaP.satRetr HaP.rowInvUp)
end Formalism.L2.FormalSeriesBounds
