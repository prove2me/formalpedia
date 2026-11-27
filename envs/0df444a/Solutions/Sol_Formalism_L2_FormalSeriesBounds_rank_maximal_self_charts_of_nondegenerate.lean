-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.rank_maximal_self_charts_of_nondegenerate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:31:06.400476+00:00
-- url     : https://prove2.me/submissions/3706a924-5fb5-4bd2-9a16-47147fe8d4e5

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_SelfConjugateRowData
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieLab
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCH
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelfCuts
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h2


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
theorem _root_.solution (h1 : RankMaximalSelfOfNondegenerate) (h2 : NondegenerateCharts Xo c) : RankMaximalSelfCharts Xo c :=
  fun hstar T io y C3 C _ _ V ι hι k Y hY _ d _ _ ha hg hr o Hc =>
    h1 C V (𝓞 E) _ Y d _ (selfOfLab ha hg o) (h2 hstar T io y C3 C V ι hι k Y hY) (rankHyp_ofLabS ha hg hr o) Hc
end Formalism.L2.FormalSeriesBounds
