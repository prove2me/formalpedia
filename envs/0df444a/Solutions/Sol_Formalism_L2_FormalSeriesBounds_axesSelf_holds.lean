-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.axesSelf_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:10:46.948933+00:00
-- url     : https://prove2.me/submissions/3367b327-90c3-4983-b4d8-d312ca334936

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieAxes
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePAxesSelfSt
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_van_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_constantCoeff_inCol
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_van_hCol
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_gauge_axes
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RawChart_axes_of
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
variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution : AxesSelfSt := by
  intro C _ _ V O _ _ dd Y d _ I0 _ p
  apply RawChart.axes_of
  · intro x
    show constantCoeff (inCol x.1 (un1 (Y.ex x.2))) = 0
    apply constantCoeff_inCol
    rw [constantCoeff_uncurry]
    exact Y.ex_const x.2
  · intro g e he
    show coeff e (∑ col, hCol col Y.h) = 0
    exact van_sum Finset.univ _ (fun col _ => van_hCol col g Y.h (gauge_axes Y g)) e he
end Formalism.L2.FormalSeriesBounds
