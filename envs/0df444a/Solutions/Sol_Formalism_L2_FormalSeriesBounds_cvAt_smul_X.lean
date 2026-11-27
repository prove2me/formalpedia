-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.cvAt_smul_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:27:15.33155+00:00
-- url     : https://prove2.me/submissions/f461ca6b-d6b3-4cd0-8d96-c9d85cf793fb

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RankMaximalOfNondegenerate
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X


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
theorem _root_.solution {s : MvPowerSeries (Fin 2) C} (hs : MvPowerSeries.constantCoeff s = 0) (c : C) :
    cvAt s (c • (MvPowerSeries.X () : PowerSeries C)) = c • s := by
  unfold cvAt
  have hS := MvPowerSeries.hasSubst_of_constantCoeff_zero (σ := Unit) fun _ => hs
  rw [MvPowerSeries.subst_smul hS, MvPowerSeries.subst_X hS]
end Formalism.L2.FormalSeriesBounds
