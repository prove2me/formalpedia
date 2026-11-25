-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.FBChart.rawSelf_axis0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:41:09.215512+00:00
-- url     : https://prove2.me/submissions/2fa7ddde-98f4-4250-8292-44c9e836757c

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePAxesSelfSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePCartSelfSt
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_gauge_axes
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_van_hCol
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_van_sum


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
theorem _root_.solution (e : Fin 2 × (Fin 2 × Fin dd) →₀ ℕ) (he : ∀ s ∈ e.support, s.1 ≠ 0) :
    coeff e (Y.rawSelf p).h = 0 := by
  show coeff e (∑ col, hCol col Y.h) = 0
  exact van_sum Finset.univ _ (fun col _ => van_hCol col 0 Y.h (gauge_axes Y 0)) e he
end FBChart
end Formalism.L2.FormalSeriesBounds
