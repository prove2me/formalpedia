-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.cartFB_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:56:34.324722+00:00
-- url     : https://prove2.me/submissions/912fbf9e-afcf-4966-a63f-5cf91502d4e4

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffAlongCvCongr
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_FBChart_chart_log_constantCoeff
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_FBChart_chart_exp_constantCoeff
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_FBChart_raw_exlg
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_FBChart_raw_lgex
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_FBChart_raw_lin
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_FBChart_raw_axis0
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_add
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_neg
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_InL_add
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_InL_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RawChart_F_mem
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
import Theorems.Thm_P2M_Formalism_L2_FormalSeriesBounds_RawChart_Vpow_mem__c20d29e22a82


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
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (hPT : PTFBSt) (hAdd : AddCvFBSt) (hStab : HStabFBSt) : CartFBSt := by
  intro C _ _ V O _ _ dd Y d _ I _ p g
  show RawChart.CartHyp (Y.raw p) V g
  haveI := Y.algClosed
  haveI : NeZero (V.l : C) := ⟨Nat.cast_ne_zero.2 V.l_prime.ne_zero⟩
  obtain ⟨ζ, hζr⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic V.l C)
    (Polynomial.degree_cyclotomic_pos V.l C V.l_prime.pos).ne'
  have hζ : IsPrimitiveRoot ζ V.l := (Polynomial.isRoot_cyclotomic_iff).1 hζr
  have hA : (Y.raw p).AddCvSt V := hAdd C V O dd Y d I p
  have h0 : (0 : ℕ → I g ⊕ JJ I g → C) ∈ (Y.raw p).TySet V g :=
    RawChart.zero_mem (Y.raw p) (Y.chart_log_constantCoeff p) (Y.raw_axis0 p) V g
  have hadd : ∀ x y, x ∈ (Y.raw p).TySet V g → y ∈ (Y.raw p).TySet V g → x + y ∈ (Y.raw p).TySet V g :=
    fun x y hx hy => RawChart.add_mem (Y.raw p) V g hA p.u_int x y hx hy
  exact
    { zero := h0
      add := hadd
      neg := fun x hx => RawChart.neg_mem (Y.raw p) V g Y.l_odd x hx
      teich := fun c hc x hx => RawChart.teich_mem (Y.raw p) V g c hc x hx
      Vm := fun x hx => RawChart.Vpow_mem' (Y.raw p) V g 1 x hx
      Fm := fun x hx => RawChart.F_mem (Y.raw p) V g (Y.chart_log_constantCoeff p) (Y.raw_exlg p) hζ h0 hadd x hx
      sumV := fun y hy => RawChart.sumV_mem (Y.raw p) V g (Y.chart_log_constantCoeff p) (Y.chart_exp_constantCoeff p) (Y.raw_exlg p)
        (Y.raw_lgex p) h0 hadd y hy
      t2 := fun x hx s hs n => RawChart.val_nonneg_leading_coeff_of_mem_tySet (Y.raw p) V g (Y.raw_lin p) (Y.raw_axis0 p) (p.u_sat g)
        (hStab C V O dd Y d I p g) x hx s hs n
      t3 := fun ζ' hζ' => RawChart.const_mem_type_set_of_nonneg (Y.raw p) (Y.chart_log_constantCoeff p) (Y.raw_axis0 p) V g ζ' hζ'
      t4 := hPT C V O dd Y d I p g }
end Formalism.L2.FormalSeriesBounds
