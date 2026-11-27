-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.mm_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:09:04.595818+00:00
-- url     : https://prove2.me/submissions/c7f16113-fe1d-46a4-9e73-c16f933896ab

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
variable {C : Type} [Field C] {V : VF C}
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution : V.MM (0 : C) := by
  unfold VF.MM
  rw [AddValuation.map_zero]
  exact WithTop.coe_lt_top 0
end Formalism.L2.FormalSeriesBounds
