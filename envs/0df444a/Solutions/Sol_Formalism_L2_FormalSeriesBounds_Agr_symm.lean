-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.Agr.symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:34:18.461811+00:00
-- url     : https://prove2.me/submissions/905127db-dd56-4583-8dd0-7996c9782fd3

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
theorem _root_.solution {τ : Type} {k : ℕ} {f g : MvPowerSeries τ C} (h : Agr k f g) : Agr k g f :=
  fun e he => (h e he).symm
end Agr
end Formalism.L2.FormalSeriesBounds
