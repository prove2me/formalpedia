-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.GlX.cas_hw
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:38:48.452797+00:00
-- url     : https://prove2.me/submissions/8365d53e-c21d-4c57-be51-d409a78c50fa

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
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
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.TO
open Formalism.GM.DimensionMonotonicity Finset
open Formalism.CountingSumsFrames.TO.GlX
variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)
namespace Formalism.CountingSumsFrames.TO.GlX
theorem _root_.solution {μ : Fin r → ℤ} {x : V} (h : G.IsHW μ x) : G.Cas x = ((GlW.casI μ : ℤ) : K) • x := by
  have h' := h
  unfold Formalism.GM.DimensionMonotonicity.GlW.IsHW Formalism.GM.DimensionMonotonicity.GlW.IsWt at h'
  obtain ⟨hw, hr⟩ := h'
  have hd : ∀ c, G.E c c x = ((μ c : ℤ) : K) • x := fun c => by
    have := G.diag c μ x
    rwa [hw] at this
  have hterm : ∀ a b, G.E a b (G.E b a x) =
      (((if a = b then μ a * μ a else if a < b then μ a - μ b else 0 : ℤ)) : K) • x := by
    intro a b
    split_ifs with hab hlt
    · subst hab
      rw [hd, map_smul, hd, smul_smul, Int.cast_mul]
    · have hc := G.comm a b b a x
      simp only [if_true, eq_self_iff_true] at hc
      rw [hr a b hlt, map_zero, sub_zero] at hc
      rw [hc, hd, hd, ← sub_smul, Int.cast_sub]
    · have hba : b < a := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hab)
      rw [hr b a hba, map_zero, Int.cast_zero, zero_smul]
  have hC : G.Cas x = ∑ a, ∑ b, G.E a b (G.E b a x) := by
    simp only [Formalism.GM.DimensionMonotonicity.GlW.Cas, LinearMap.sum_apply, LinearMap.comp_apply]
  rw [hC]
  simp only [hterm, Formalism.GM.DimensionMonotonicity.GlW.casI, Int.cast_sum, Finset.sum_smul]
end Formalism.CountingSumsFrames.TO.GlX
