-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.subst_cvAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:30:53.232707+00:00
-- url     : https://prove2.me/submissions/7029d1ce-30b5-4077-89c8-72c83f0d1112

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RankMaximalOfNondegenerate
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
theorem _root_.solution {s : MvPowerSeries (Fin 2) C} (hs : MvPowerSeries.constantCoeff s = 0) {σ : Type} [Finite σ]
    {γ : σ → PowerSeries C} (hγ : ∀ j, PowerSeries.constantCoeff (γ j) = 0) (F : MvPowerSeries σ C) :
    MvPowerSeries.subst (fun j => cvAt s (γ j)) F = cvAt s (MvPowerSeries.subst γ F) := by
  unfold cvAt
  rw [MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero hγ)
    (MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => hs)]
end Formalism.L2.FormalSeriesBounds
