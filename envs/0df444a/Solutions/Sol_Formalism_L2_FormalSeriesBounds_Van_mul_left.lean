-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.Van.mul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:49:11.288672+00:00
-- url     : https://prove2.me/submissions/de2b5609-1ef2-4838-926e-4a2fc84d13e5

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHStab
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_mul_right


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
theorem _root_.solution {T : Set τ} {f : MvPowerSeries τ C} (hf : Van T f) (g : MvPowerSeries τ C) : Van T (g * f) := by
  rw [mul_comm]
  exact hf.mul_right g
end Van
end Formalism.L2.FormalSeriesBounds
