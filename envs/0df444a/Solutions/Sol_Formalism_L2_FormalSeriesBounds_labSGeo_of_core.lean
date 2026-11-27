-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.labSGeo_of_core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:31:15.39119+00:00
-- url     : https://prove2.me/submissions/6b519080-3fc5-43bd-89f4-96fa14bc9b26

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_SelfConjugateRowData
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieLab
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCH
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelfCuts
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_labSGeo_of

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
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {C : Type} [Field C] [CharZero C] {V : VF C}
variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}
variable (Xo c)
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (h : LabSGeoCoreSt Xo c) : LabSGeoSt Xo c :=
  fun hstar T io y C3 C _ _ V ι hι k Y hY Orb d _ lab ha =>
    labSGeo_of hstar hι ha (h hstar T io y C3 C V ι hι k Y hY Orb d lab ha)
end Formalism.L2.FormalSeriesBounds
