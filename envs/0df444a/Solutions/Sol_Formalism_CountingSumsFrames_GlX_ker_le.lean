-- Prove2me | solution 1 for Formalism.CountingSumsFrames.GlX.ker_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:27:10.277064+00:00
-- url     : https://prove2.me/submissions/953c9824-c702-4791-929e-66c2b05a1c8d

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount
import Theorems.Thm_Formalism_CountingSumsFrames_GlX_inf_stable
import Theorems.Thm_Formalism_CountingSumsFrames_GlX_range_Lv
import Theorems.Thm_Formalism_CountingSumsFrames_GlX_Lv_add
import Theorems.Thm_Formalism_CountingSumsFrames_GlX_Lv_smul
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_exists_hwmod
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_gS_le
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_gS_stable
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_graded_of
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_hw_in_gS
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_raising_of
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
open Formalism Formalism.CountingSumsFrames
open Formalism.GM.DimensionMonotonicity Finset
open Formalism.CountingSumsFrames.GlX
variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)
namespace Formalism.CountingSumsFrames.GlX
theorem _root_.solution {W : Submodule K V} (hW : G.Stable W) (hWf : G.FinW W) {la : Fin r → ℤ} {h h' : V}
    (hh : G.IsHW la h) (hh' : G.IsHW la h') (hhW : h ∈ W) (hh'W : h' ∈ W) (h0 : h ≠ 0) :
    LinearMap.ker (Lv G h) ≤ LinearMap.ker (Lv G h') := by
  intro c hc
  rw [LinearMap.mem_ker] at hc ⊢
  by_contra hx
  have hs : G.IsHW la (h + h') := ⟨by show G.comp la (h + h') = h + h'; rw [map_add, hh.1, hh'.1],
    fun a b hab => by rw [map_add, hh.2 a b hab, hh'.2 a b hab, add_zero]⟩
  have hxs : Lv G h' c ∈ G.gS {h + h'} := by rw [← range_Lv]; exact ⟨c, by rw [Lv_add, hc, zero_add]⟩
  have hxh : Lv G h' c ∈ G.gS {h'} := by rw [← range_Lv]; exact ⟨c, rfl⟩
  have hKs : G.Stable (G.gS {h + h'} ⊓ G.gS {h'}) := inf_stable G (G.gS_stable _) (G.gS_stable _)
  have hgW : G.gS {h'} ≤ W := G.gS_le (by simpa using hh'W) hW
  obtain ⟨S, hS⟩ := hWf
  have hn : ¬ (G.gS {h + h'} ⊓ G.gS {h'}) ≤ ⊥ := fun hle => hx ((Submodule.mem_bot K).mp (hle ⟨hxs, hxh⟩))
  obtain ⟨y, hyK, hy0, ν, hyw, hyr⟩ := G.exists_hwmod (G.graded_of hKs) (G.raising_of hKs)
    ⟨S, fun z hz => hS z (hgW hz.2)⟩ hn
  have hyhw : G.IsHW ν y := ⟨hyw, fun a b hab => (Submodule.mem_bot K).mp (hyr a b hab)⟩
  have hy0' : y ≠ 0 := fun e => hy0 (by rw [e]; exact Submodule.zero_mem _)
  obtain ⟨-, c1, hc1⟩ := G.hw_in_gS hh' hW ⟨S, hS⟩ hh'W hyK.2 hyhw hy0'
  obtain ⟨-, c2, hc2⟩ := G.hw_in_gS hs hW ⟨S, hS⟩ (W.add_mem hhW hh'W) hyK.1 hyhw hy0'
  by_cases hc2z : c2 = 0
  · rw [hc2z, zero_smul] at hc2; exact hy0' hc2
  · have e0 : c2 • h = (c1 - c2) • h' := by rw [sub_smul, ← hc1, hc2, smul_add, add_sub_cancel_right]
    have e : h = (c2⁻¹ * (c1 - c2)) • h' := by
      rw [mul_smul, ← e0, smul_smul, inv_mul_cancel₀ hc2z, one_smul]
    have e2 : Lv G h c = (c2⁻¹ * (c1 - c2)) • Lv G h' c := by
      conv_lhs => rw [e]
      rw [Lv_smul]
    rw [hc] at e2
    have ht : c2⁻¹ * (c1 - c2) = 0 := by
      rcases smul_eq_zero.mp e2.symm with h1 | h1
      · exact h1
      · exact absurd h1 hx
    rw [ht, zero_smul] at e
    exact h0 e
end Formalism.CountingSumsFrames.GlX
