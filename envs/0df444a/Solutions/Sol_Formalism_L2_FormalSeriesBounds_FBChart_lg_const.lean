-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.FBChart.lg_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:39:56.318712+00:00
-- url     : https://prove2.me/submissions/90897cab-8f5c-49f1-b438-61b44c2f5978

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffAlongCvCongr
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB

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
theorem _root_.solution (i : Fin dd) : MvPowerSeries.constantCoeff (Y.lg i) = 0 := by
  have h := Y.lg_lin i 0 (by simp)
  rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_zero_X] at h
  exact h
end FBChart
end Formalism.L2.FormalSeriesBounds
