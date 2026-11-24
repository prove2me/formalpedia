-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.Van.smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:08:36.577161+00:00
-- url     : https://prove2.me/submissions/19f6ba76-e91e-4688-9e7a-3f26592bae66

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieAxes

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
theorem _root_.solution {T : Set τ} {f : MvPowerSeries τ C} (hf : Van T f) (c : C) : Van T (c • f) := by
  intro ν hν
  rw [coeff_smul, hf ν hν, mul_zero]
end Van
end Formalism.L2.FormalSeriesBounds
