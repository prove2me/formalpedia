-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.agr_subst_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:30:40.905985+00:00
-- url     : https://prove2.me/submissions/d2b0a235-99bf-49d2-acd3-da6c1f8e7e13

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RankMaximalOfNondegenerate
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_agr_iff_trunc
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution {σ τ : Type} [Finite σ] [Finite τ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) {k : ℕ} {f g : MvPowerSeries σ C} (h : Agr k f g) :
    Agr k (MvPowerSeries.subst a f) (MvPowerSeries.subst a g) := by
  rw [agr_iff_trunc, MvPowerSeries.truncTotal_subst ha, MvPowerSeries.truncTotal_subst ha,
    (agr_iff_trunc k f g).1 h]
end Formalism.L2.FormalSeriesBounds
