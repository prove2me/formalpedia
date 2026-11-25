-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.elementary_pair_support
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:57:15.973968+00:00
-- url     : https://prove2.me/submissions/70357f5f-16ab-45cb-b81d-e9b212f2459f

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHStab
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_elementary_pair_eq_zero_of_ne

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
theorem _root_.solution {P Q s : τ} (h : E2 P Q s ≠ 0) : s = P ∨ s = Q := by
  by_contra hc
  push Not at hc
  exact h (elementary_pair_eq_zero_of_ne hc.1 hc.2)
end Formalism.L2.FormalSeriesBounds
