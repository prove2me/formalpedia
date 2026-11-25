-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.FBChart.raw_lgex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:46:26.594501+00:00
-- url     : https://prove2.me/submissions/36117223-e36c-4d47-9d97-9156b038ed26

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffAlongCvCongr
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_uncurry_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_uncurry_comp
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
    MvPowerSeries.subst (Y.raw p).ex ((Y.raw p).lg i) = (MvPowerSeries.X i : MvPowerSeries (Fin dd) C) := by
  show MvPowerSeries.subst (fun j => un1 (Y.ex j)) (un1 (Y.lg i)) = _
  rw [uncurry_comp (fun j => Y.ex_const j), Y.lg_ex]
  exact uncurry_X i
end FBChart
end Formalism.L2.FormalSeriesBounds
