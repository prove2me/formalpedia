-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.FBChart.self_chart_exp_constantCoeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:55:24.138731+00:00
-- url     : https://prove2.me/submissions/230f22f5-bb40-4329-9ff7-ff89296f853a

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePAxesSelfSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePCartSelfSt
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_constantCoeff_inCol
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_constantCoeff_uncurry


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
namespace FBChart
theorem _root_.solution (x : Fin 2 × Fin dd) : constantCoeff ((Y.rawSelf p).ex x) = 0 := by
  show constantCoeff (inCol x.1 (un1 (Y.ex x.2))) = 0
  apply constantCoeff_inCol
  rw [constantCoeff_uncurry]
  exact Y.ex_const x.2
end FBChart
end Formalism.L2.FormalSeriesBounds
