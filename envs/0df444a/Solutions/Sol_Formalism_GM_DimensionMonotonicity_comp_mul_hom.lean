-- Prove2me | solution 1 for Formalism.GM.DimensionMonotonicity.comp_mul_hom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:48:38.056099+00:00
-- url     : https://prove2.me/submissions/1fa9be6c-78a8-40ab-89ab-d9eeb39b83e8

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_comb
import Theorems.Thm_Formalism_GM_M_FB_evVal_castSucc
import Theorems.Thm_Formalism_GM_M_FB_evVal_last
import Theorems.Thm_Formalism_GM_M_FB_ext_castSucc
import Theorems.Thm_Formalism_GM_M_FB_ext_last
import Theorems.Thm_Formalism_GM_M_FB_res_apply
import Theorems.Thm_Formalism_GM_M_FB_res_ext
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_last
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_last
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_castSucc
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_last
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_comb
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_comb
attribute [local simp] Formalism.GM.M.FB.evVal_castSucc
attribute [local simp] Formalism.GM.M.FB.evVal_last
attribute [local simp] Formalism.GM.M.FB.ext_castSucc
attribute [local simp] Formalism.GM.M.FB.ext_last
attribute [local simp] Formalism.GM.M.FB.res_apply
attribute [local simp] Formalism.GM.M.FB.res_ext
attribute [local simp] Formalism.GM.M.FB.snoc_deg_castSucc
attribute [local simp] Formalism.GM.M.FB.snoc_deg_last
attribute [local simp] Formalism.GM.M.FB.snoc_vec_castSucc
attribute [local simp] Formalism.GM.M.FB.snoc_vec_last



set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
namespace Formalism.GM.DimensionMonotonicity
theorem _root_.solution {σ M K : Type} [AddCommGroup M] [CommRing K] (w : σ → M) {φ : MvPolynomial σ K} {κ : M}
    (hφ : IsWeightedHomogeneous w φ κ) (ν : M) (x : MvPolynomial σ K) :
    weightedHomogeneousComponent w (ν + κ) (φ * x) = φ * weightedHomogeneousComponent w ν x := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent, coeff_mul, coeff_mul]
  split_ifs with hd
  · refine Finset.sum_congr rfl fun ab hab => ?_
    rw [coeff_weightedHomogeneousComponent]
    by_cases h0 : coeff ab.1 φ = 0
    · rw [h0, zero_mul, zero_mul]
    · have h1 : Finsupp.weight w ab.1 = κ := hφ h0
      have hab' : ab.1 + ab.2 = d := by simpa using hab
      have h2 : Finsupp.weight w ab.1 + Finsupp.weight w ab.2 = Finsupp.weight w d := by
        rw [← map_add, hab']
      have h3 : Finsupp.weight w ab.2 = ν := by
        rw [h1, hd, add_comm] at h2
        exact add_right_cancel h2
      rw [if_pos h3]
  · symm
    refine Finset.sum_eq_zero fun ab hab => ?_
    rw [coeff_weightedHomogeneousComponent]
    by_cases h0 : coeff ab.1 φ = 0
    · rw [h0, zero_mul]
    · have h1 : Finsupp.weight w ab.1 = κ := hφ h0
      have hab' : ab.1 + ab.2 = d := by simpa using hab
      have h2 : Finsupp.weight w ab.1 + Finsupp.weight w ab.2 = Finsupp.weight w d := by
        rw [← map_add, hab']
      rw [if_neg, mul_zero]
      intro h3
      apply hd
      rw [← h2, h1, h3, add_comm]
end Formalism.GM.DimensionMonotonicity
