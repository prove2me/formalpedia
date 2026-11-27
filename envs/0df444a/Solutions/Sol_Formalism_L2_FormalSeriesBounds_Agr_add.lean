-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.Agr.add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:08:58.859443+00:00
-- url     : https://prove2.me/submissions/ea608914-07ae-4430-a5c3-44514fc0d3f1

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RankMaximalOfNondegenerate

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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
namespace Formalism.L2.FormalSeriesBounds
namespace Agr
theorem _root_.solution {τ : Type} {k : ℕ} {f g f' g' : MvPowerSeries τ C} (h : Agr k f g) (h' : Agr k f' g') :
    Agr k (f + f') (g + g') := fun e he => by rw [map_add, map_add, h e he, h' e he]
end Agr
end Formalism.L2.FormalSeriesBounds
