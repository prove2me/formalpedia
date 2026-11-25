-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.FBChart.axisAll
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:58:31.951416+00:00
-- url     : https://prove2.me/submissions/f71780f7-33a4-4549-a8bf-e7bb1bc7e2c8

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHStab
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_fin_two_eq_zero_or_eq_one
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_of_ev_zero
import Theorems.Thm_P2M_Formalism_L2_FormalSeriesBounds_fin_two_eq_one_sub_of_ne__93512bbd28f7


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
variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
namespace Formalism.L2.FormalSeriesBounds
namespace FBChart
theorem _root_.solution (Y : FBChart C V O dd) (g : Fin 2) (e : Fin 2 × Fin dd →₀ ℕ)
    (he : ∀ s ∈ e.support, s.1 ≠ g) : coeff e Y.h = 0 := by
  rcases fin_two_eq_zero_or_eq_one g with rfl | rfl
  · refine coeff_of_ev_zero Y.h 0 ![0, pt C dd 0] rfl ?_ Y.gauge.ax0 e he
    intro g' hg'
    rw [fin_two_eq_one_sub_of_ne' 0 g' hg']
    rfl
  · refine coeff_of_ev_zero Y.h 1 ![pt C dd 0, 0] rfl ?_ Y.gauge.ax1 e he
    intro g' hg'
    rw [fin_two_eq_one_sub_of_ne' 1 g' hg']
    rfl
end FBChart
end Formalism.L2.FormalSeriesBounds
