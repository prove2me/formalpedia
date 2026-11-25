-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.Van.sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:49:12.123707+00:00
-- url     : https://prove2.me/submissions/1b115732-a3b9-4712-b97c-93b5e6303752

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
variable {τ : Type}
namespace Formalism.L2.FormalSeriesBounds
namespace Van
theorem _root_.solution {T : Set τ} {f g : MvPowerSeries τ C} (hf : Van T f) (hg : Van T g) : Van T (f - g) := by
  intro ν hν
  rw [map_sub, hf ν hν, hg ν hν, sub_zero]
end Van
end Formalism.L2.FormalSeriesBounds
