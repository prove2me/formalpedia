-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.rank_maximal_charts_of_nondegenerate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:57:11.996628+00:00
-- url     : https://prove2.me/submissions/a30e98fb-c720-4b09-8257-d9d548e7432a

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieTop
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
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
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (h1 : RankMaximalOfNondegenerate) (h2 : NondegenerateCharts Xo c) : RankMaximalCharts Xo c :=
  fun hstar T io y C3 C _ _ V ι hι k Y hY _ d _ lab ha hg hr o Hc =>
    h1 C V (𝓞 E) _ Y d _ (pairOfLab ha hg o) (h2 hstar T io y C3 C V ι hι k Y hY) (rankHyp_ofLab ha hg hr o) Hc
end Formalism.L2.FormalSeriesBounds
