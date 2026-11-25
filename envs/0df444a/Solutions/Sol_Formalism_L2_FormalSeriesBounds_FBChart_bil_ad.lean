-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.FBChart.bil_ad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:01:47.395357+00:00
-- url     : https://prove2.me/submissions/75afc584-3025-4406-9a4c-e11c689bc567

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHStab
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_sub
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_bil_sub
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_bil_ev_left
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_bil_ev_right
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_map_self
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_FBChart_axisAll
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_van_ev_left
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_van_ev_right
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_bil_expS
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sub
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_InL_sub
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_sub
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_const


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
theorem _root_.solution (Y : FBChart C V O dd) (a : O) (w v : Fin dd → C) :
    bil (Y.B.ad a) w v = bil Y.h (linAct (Y.B.A.act a) w) v - bil Y.h w (linAct (Y.B.A.act (star a)) v) := by
  have hg := Y.gauge.ad a
  have hact : ∀ x, Y.B.actK C x = Y.B.A.act x := fun x => funext fun i => map_self _
  rw [hact, hact] at hg
  have hk : FB.toK C (Y.B.ad a) = Y.B.ad a := map_self _
  rw [hk] at hg
  rw [hg, bil_expS ((van_ev_left Y.axisAll (Y.B.A.const a)).sub (van_ev_right Y.axisAll (Y.B.A.const (star a)))),
    bil_sub, bil_ev_left Y.axisAll (Y.B.A.const a), bil_ev_right Y.axisAll (Y.B.A.const (star a))]
end FBChart
end Formalism.L2.FormalSeriesBounds
