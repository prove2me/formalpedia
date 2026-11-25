-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.ne01
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:47:09.42182+00:00
-- url     : https://prove2.me/submissions/04c06279-6bf4-4aa9-8165-0bdd426d083d

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHStab

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries
variable {C : Type} [Field C]
variable {dd : ℕ}
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (x y : Fin dd) : ((0 : Fin 2), x) ≠ ((1 : Fin 2), y) := fun e => by
  have h01 : (0 : Fin 2) = 1 := congrArg Prod.fst e
  exact absurd h01 (by decide)
end Formalism.L2.FormalSeriesBounds
