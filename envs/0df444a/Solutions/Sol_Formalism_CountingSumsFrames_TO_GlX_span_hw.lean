-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.GlX.span_hw
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:18:01.309056+00:00
-- url     : https://prove2.me/submissions/32b09699-8b96-4262-a8e0-2190c1e8bdff

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_CountingSumsFrames_TO_GlX_qlist_ne
import Theorems.Thm_Formalism_CountingSumsFrames_TO_GlX_cprod_mod
import Theorems.Thm_Formalism_CountingSumsFrames_TO_GlX_iSup_stable
import Theorems.Thm_Formalism_CountingSumsFrames_TO_GlX_gen_kill
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_Dle_antisymm
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_Dle_raise
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_E_cprod
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_comp_cprod
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_cprod_mem
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_dom_of_hwmod
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_exists_hwmod
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_gS_stable
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_graded_of
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_isWt_E
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_raising_of
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_subset_gS
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_cprod_ne
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_dl_ne_zero
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
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_prod
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IsIntP_prod
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
theorem _root_.solution {W : Submodule K V} (hW : G.Stable W) {S : Finset (Fin r → ℤ)}
    (hS : ∀ x ∈ W, ∀ μ ∉ S, G.comp μ x = 0) {ι : Type*} (h : ι → V) (la : ι → Fin r → ℤ)
    (hh : ∀ i, G.IsHW (la i) (h i)) (hhW : ∀ i, h i ∈ W) (hh0 : ∀ i, h i ≠ 0)
    (hsp : ∀ μ v, v ∈ W → G.IsHW μ v → v ∈ Submodule.span K (Set.range h)) :
    W ≤ ⨆ i, G.gS {h i} := by
  classical
  have hUs : G.Stable (⨆ i, G.gS {h i}) := iSup_stable G (fun i => G.gS_stable _)
  by_contra hn
  obtain ⟨v, hvW, hvU, μ, hvw, hr⟩ := G.exists_hwmod (G.graded_of hW) (G.raising_of hW) ⟨S, hS⟩ hn
  have hμ : DomW μ := G.dom_of_hwmod hUs hW ⟨S, hS⟩ hvW hvU hvw hr
  have hs : (((qlist S (GlW.casI μ)).map (fun c => (((GlW.casI μ - c : ℤ)) : K))).prod) ≠ 0 :=
    cprod_ne (V := V) (GlW.casI μ) _ (qlist_ne S _)
  have hmod := cprod_mod G hUs hvw hr (qlist S (GlW.casI μ))
  have hv'U : ((((qlist S (GlW.casI μ)).map (fun c => (((GlW.casI μ - c : ℤ)) : K))).prod)⁻¹ •
      G.cprod (qlist S (GlW.casI μ)) v) - v ∈ ⨆ i, G.gS {h i} := by
    have := Submodule.smul_mem _ ((((qlist S (GlW.casI μ)).map (fun c => (((GlW.casI μ - c : ℤ)) : K))).prod)⁻¹) hmod
    rwa [smul_sub, smul_smul, inv_mul_cancel₀ hs, one_smul] at this
  have hkill : ∀ a b, a < b → ∀ y ∈ ⨆ i, G.gS {h i},
      G.cprod (qlist S (GlW.casI μ)) (G.comp (μ + dl a b) y) = 0 := by
    intro a b hab y hy
    refine Submodule.iSup_induction _ (motive := fun y => G.cprod (qlist S (GlW.casI μ)) (G.comp (μ + dl a b) y) = 0) hy
      (fun i x hx => gen_kill G hW hS (hh i) (hhW i) (hh0 i) hμ (Dle_raise μ hab) ?_ x hx) (by simp) ?_
    · intro hle hlaμ
      rw [hlaμ] at hle
      have := Dle_antisymm hle (Dle_raise μ hab)
      exact dl_ne_zero (ne_of_lt hab) (by simpa using this)
    · intro x y hx hy; rw [map_add, map_add, hx, hy, add_zero]
  apply hvU
  have hv'hw : G.IsHW μ ((((qlist S (GlW.casI μ)).map (fun c => (((GlW.casI μ - c : ℤ)) : K))).prod)⁻¹ •
      G.cprod (qlist S (GlW.casI μ)) v) := by
    refine ⟨?_, fun a b hab => ?_⟩
    · show G.comp μ _ = _
      rw [map_smul, G.comp_cprod, hvw]
    · rw [map_smul, G.E_cprod]
      have hw := G.isWt_E hvw a b
      have := hkill a b hab _ (hr a b hab)
      rw [hw] at this
      rw [this, smul_zero]
  have hin := hsp μ _ (W.smul_mem _ (G.cprod_mem hW _ hvW)) hv'hw
  have hin' : _ ∈ ⨆ i, G.gS {h i} := Submodule.span_le.mpr (by
    rintro _ ⟨i, rfl⟩; exact Submodule.mem_iSup_of_mem i (G.subset_gS _ (Set.mem_singleton _))) hin
  have hfin := Submodule.sub_mem _ hin' hv'U
  rwa [sub_sub_cancel] at hfin
end Formalism.CountingSumsFrames.TO.GlX
