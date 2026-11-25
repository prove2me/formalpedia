-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.FBChart.raw_axis0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:39:08.731793+00:00
-- url     : https://prove2.me/submissions/1c958774-526b-44d1-a6dc-f64d5de3ff67

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffAlongCvCongr
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} {I : Fin 2 → Type}
  [∀ g, Fintype (I g)] (Y : FBChart C V O dd) (p : PairData Y d I)
namespace Formalism.L2.FormalSeriesBounds
namespace FBChart
theorem _root_.solution (e : Fin 2 × Fin dd →₀ ℕ) (he : ∀ s ∈ e.support, s.1 ≠ 0) :
    MvPowerSeries.coeff e (Y.raw p).h = 0 := by
  refine coeff_of_ev_zero Y.h 0 ![0, pt C dd 0] rfl ?_ Y.gauge.ax0 e he
  intro g' hg'
  rw [fin_two_eq_one_sub_of_ne' 0 g' hg']
  rfl
end FBChart
end Formalism.L2.FormalSeriesBounds
