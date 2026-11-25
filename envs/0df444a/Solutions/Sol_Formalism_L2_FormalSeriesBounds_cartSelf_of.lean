-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.cartSelf_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:10:52.266552+00:00
-- url     : https://prove2.me/submissions/4fa4b781-e2e6-4d15-af0c-878baf28b76b

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePAxesSelfSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePCartSelfSt
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_FBChart_self_chart_log_constantCoeff
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_FBChart_self_chart_exp_constantCoeff
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_FBChart_rawSelf_axis0
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_FBChart_rawSelf_exlg
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_FBChart_rawSelf_lgex
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_FBChart_rawSelf_lin
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_FBChart_rawSelf_u_integral
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_FBChart_exists_integral_right_inverse
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_add
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_neg
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_InL_add
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_InL_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RawChart_F_mem
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RawChart_V_mem
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RawChart_add_mem
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RawChart_const_mem_type_set_of_nonneg
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RawChart_neg_mem
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RawChart_sumV_mem
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RawChart_teich_mem
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RawChart_val_nonneg_leading_coeff_of_mem_tySet
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RawChart_zero_mem
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_add
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_neg
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_l_ne_zero
import Theorems.Thm_Formalism_L2_Pj_IsEval_zero


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
theorem _root_.solution (hPT : PTSelfSt) (hAdd : AddCvSelfSt) (hStab : HStabSelfSt) : CartSelfSt := by
  intro C _ _ V O _ _ dd Y d _ I0 _ p g
  have := Y.algClosed
  have : NeZero (V.l : C) := ⟨VF.l_ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot C V.l
  have h0 := (Y.rawSelf p).zero_mem (Y.self_chart_log_constantCoeff p) (Y.rawSelf_axis0 p) V g
  have hadd := (Y.rawSelf p).add_mem V g (hAdd C V O dd Y d I0 p) (fun g c x => Y.rawSelf_u_integral p g c x)
  exact
    { zero := h0
      add := hadd
      neg := (Y.rawSelf p).neg_mem V g Y.l_odd
      teich := (Y.rawSelf p).teich_mem V g
      Vm := (Y.rawSelf p).V_mem V g
      Fm := (Y.rawSelf p).F_mem V g (Y.self_chart_log_constantCoeff p) (Y.rawSelf_exlg p) hζ h0 hadd
      sumV := (Y.rawSelf p).sumV_mem V g (Y.self_chart_log_constantCoeff p) (Y.self_chart_exp_constantCoeff p) (Y.rawSelf_exlg p) (Y.rawSelf_lgex p) h0 hadd
      t2 := (Y.rawSelf p).val_nonneg_leading_coeff_of_mem_tySet V g (Y.rawSelf_lin p) (Y.rawSelf_axis0 p) (Y.exists_integral_right_inverse p g) (hStab C V O dd Y d I0 p g)
      t3 := (Y.rawSelf p).const_mem_type_set_of_nonneg (Y.self_chart_log_constantCoeff p) (Y.rawSelf_axis0 p) V g
      t4 := hPT C V O dd Y d I0 p g }
end Formalism.L2.FormalSeriesBounds
