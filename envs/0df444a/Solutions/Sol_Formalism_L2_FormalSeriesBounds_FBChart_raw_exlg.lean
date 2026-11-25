-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.FBChart.raw_exlg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:46:16.614247+00:00
-- url     : https://prove2.me/submissions/5ed528da-252c-40f3-9fea-0b69e2cd2ddd

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffAlongCvCongr
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_uncurry_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_uncurry_comp
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_FBChart_lg_const
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst


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
theorem _root_.solution (i : Fin dd) :
    MvPowerSeries.subst (Y.raw p).lg ((Y.raw p).ex i) = (MvPowerSeries.X i : MvPowerSeries (Fin dd) C) := by
  show MvPowerSeries.subst (fun j => un1 (Y.lg j)) (un1 (Y.ex i)) = _
  rw [uncurry_comp (fun j => Y.lg_const j), Y.ex_lg]
  exact uncurry_X i
end FBChart
end Formalism.L2.FormalSeriesBounds
