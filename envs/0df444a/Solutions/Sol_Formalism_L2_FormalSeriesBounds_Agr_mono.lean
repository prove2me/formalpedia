-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.Agr.mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:28:58.260806+00:00
-- url     : https://prove2.me/submissions/e7891f08-e49a-4079-8ea4-8ce267fabfc1

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
theorem _root_.solution {τ : Type} {k k' : ℕ} {f g : MvPowerSeries τ C} (h : Agr k f g) (hk : k' ≤ k) : Agr k' f g :=
  fun e he => h e (lt_of_lt_of_le he hk)
end Agr
end Formalism.L2.FormalSeriesBounds
