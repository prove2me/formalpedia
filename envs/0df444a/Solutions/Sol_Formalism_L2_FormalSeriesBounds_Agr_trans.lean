-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.Agr.trans
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:36:09.76418+00:00
-- url     : https://prove2.me/submissions/db3503d9-f550-453c-b412-8b89a36379f4

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
theorem _root_.solution {τ : Type} {k : ℕ} {f g g' : MvPowerSeries τ C} (h : Agr k f g) (h' : Agr k g g') : Agr k f g' :=
  fun e he => (h e he).trans (h' e he)
end Agr
end Formalism.L2.FormalSeriesBounds
