-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.SelfData.gm_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:49:07.011582+00:00
-- url     : https://prove2.me/submissions/f01595ad-62d3-4a53-be99-82e0444fbba7

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePAxesSelfSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePCartSelfSt

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
variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} (Y : FBChart C V O dd) {d : ℕ}
  {I0 : Type} [Fintype I0] (p : SelfData Y d I0)
namespace Formalism.L2.FormalSeriesBounds
namespace SelfData
theorem _root_.solution (a : ZMod d) (g : Fin 2) :
    ∑ col, p.gm a col g * p.gm (a + p.hd) col (1 - g) = 1 := by
  have h := p.gm_hyp (a + p.hd) g (1 - g)
  rw [add_assoc, p.hd_two, add_zero, if_neg (by fin_cases g <;> decide)] at h
  exact h
end SelfData
end Formalism.L2.FormalSeriesBounds
