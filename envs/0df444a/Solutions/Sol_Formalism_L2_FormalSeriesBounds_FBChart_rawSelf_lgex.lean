-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.FBChart.rawSelf_lgex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:46:25.313718+00:00
-- url     : https://prove2.me/submissions/7ff499f1-143e-4d04-8734-08f0231bf051

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePAxesSelfSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePCartSelfSt
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_hasSubst_col
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_subst_inCol
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_FBChart_self_chart_exp_constantCoeff
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_constantCoeff_uncurry
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_uncurry_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_uncurry_comp


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
theorem _root_.solution (x : Fin 2 × Fin dd) :
    subst (Y.rawSelf p).ex ((Y.rawSelf p).lg x) = (X x : MvPowerSeries (Fin 2 × Fin dd) C) := by
  obtain ⟨col, i⟩ := x
  show subst (Y.rawSelf p).ex (inCol col (un1 (Y.lg i))) = _
  rw [subst_inCol (Y.self_chart_exp_constantCoeff p)]
  show subst (fun j => inCol col (un1 (Y.ex j))) (un1 (Y.lg i)) = _
  have hL : HasSubst (fun j => un1 (Y.ex j)) :=
    hasSubst_of_constantCoeff_zero fun j => by rw [constantCoeff_uncurry, Y.ex_const]
  have hx : un1 (comp1 Y.lg Y.ex i) = (X i : MvPowerSeries (Fin dd) C) := by rw [Y.lg_ex]; exact uncurry_X i
  unfold inCol
  rw [← subst_comp_subst_apply hL (hasSubst_col col), uncurry_comp Y.ex_const, hx, subst_X (hasSubst_col col)]
end FBChart
end Formalism.L2.FormalSeriesBounds
