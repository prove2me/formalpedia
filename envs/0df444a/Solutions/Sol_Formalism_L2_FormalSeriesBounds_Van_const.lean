-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.Van.const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:09:30.632806+00:00
-- url     : https://prove2.me/submissions/b4aa4e03-e617-4fd0-9b09-4a0457c19301

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
theorem _root_.solution {T : Set τ} {f : MvPowerSeries τ C} (hf : Van T f) : constantCoeff f = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  exact hf 0 (by simp)
end Van
end Formalism.L2.FormalSeriesBounds
