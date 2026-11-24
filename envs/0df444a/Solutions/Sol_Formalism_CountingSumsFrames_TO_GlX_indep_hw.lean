-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.GlX.indep_hw
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:27:43.425817+00:00
-- url     : https://prove2.me/submissions/7ea0cc58-fed6-44f6-b1c2-9c6774c42106

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_CountingSumsFrames_TO_GlX_cas_hw
import Theorems.Thm_Formalism_CountingSumsFrames_TO_GlX_qlist_ne
import Theorems.Thm_Formalism_CountingSumsFrames_TO_GlX_iSup_stable
import Theorems.Thm_Formalism_CountingSumsFrames_TO_GlX_inf_stable
import Theorems.Thm_Formalism_CountingSumsFrames_TO_GlX_gen_kill
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_Dle_refl
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_bot_stable
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_comp_top_of_mem
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_dom_of_hwmod
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_exists_hwmod
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_gS_le
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_gS_stable
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_graded_of
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_hw_in_gS
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_raising_of
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_cprod_eig
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_cprod_ne
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
    (hh : ∀ i, G.IsHW (la i) (h i)) (hhW : ∀ i, h i ∈ W) (hli : LinearIndependent K h) :
    iSupIndep (fun i => G.gS {h i}) := by
  classical
  have hh0 : ∀ i, h i ≠ 0 := fun i => hli.ne_zero i
  intro i
  rw [Submodule.disjoint_def]
  intro x0 hx01 hx02
  by_contra hx00
  have hKs : G.Stable (G.gS {h i} ⊓ ⨆ (j) (_ : j ≠ i), G.gS {h j}) :=
    inf_stable G (G.gS_stable _) (iSup_stable G fun j => iSup_stable G fun _ => G.gS_stable _)
  have hgW : G.gS {h i} ≤ W := G.gS_le (by simpa using hhW i) hW
  have hn' : ¬ (G.gS {h i} ⊓ ⨆ (j) (_ : j ≠ i), G.gS {h j}) ≤ ⊥ := fun h' =>
    hx00 ((Submodule.mem_bot K).mp (h' ⟨hx01, hx02⟩))
  obtain ⟨y, hyK, hy0, ν, hyw, hyr⟩ := G.exists_hwmod (G.graded_of hKs) (G.raising_of hKs)
    ⟨S, fun x hx => hS x (hgW hx.1)⟩ hn'
  have hyhw : G.IsHW ν y := ⟨hyw, fun a b hab => (Submodule.mem_bot K).mp (hyr a b hab)⟩
  have hy0' : y ≠ 0 := fun h' => hy0 (by rw [h']; exact Submodule.zero_mem _)
  obtain ⟨-, c, hyc⟩ := G.hw_in_gS (hh i) hW ⟨S, hS⟩ (hhW i) hyK.1 hyhw hy0'
  have hc0 : c ≠ 0 := by rintro rfl; exact hy0' (by rw [hyc, zero_smul])
  have hiK : h i ∈ ⨆ (j) (_ : j ≠ i), G.gS {h j} := by
    have := Submodule.smul_mem _ c⁻¹ hyK.2
    rwa [hyc, smul_smul, inv_mul_cancel₀ hc0, one_smul] at this
  have hμ : DomW (la i) := G.dom_of_hwmod G.bot_stable hW ⟨S, hS⟩ (hhW i) (by rw [Submodule.mem_bot]; exact hh0 i)
    (hh i).1 (fun a b hab => by rw [(hh i).2 a b hab]; exact Submodule.zero_mem _)
  have hs : (((qlist S (GlW.casI (la i))).map (fun c => (((GlW.casI (la i) - c : ℤ)) : K))).prod) ≠ 0 :=
    cprod_ne (V := V) (GlW.casI (la i)) _ (qlist_ne S _)
  have hQ : ∀ x ∈ ⨆ (j) (_ : j ≠ i), G.gS {h j},
      G.cprod (qlist S (GlW.casI (la i))) (G.comp (la i) x) ∈ Submodule.span K (h '' {j | j ≠ i}) := by
    intro x hx
    refine Submodule.iSup_induction _ (motive := fun x =>
      G.cprod (qlist S (GlW.casI (la i))) (G.comp (la i) x) ∈ Submodule.span K (h '' {j | j ≠ i})) hx
      (fun j x hx => ?_) (by simp) (fun x y hx hy => by rw [map_add, map_add]; exact Submodule.add_mem _ hx hy)
    refine Submodule.iSup_induction _ (motive := fun x =>
      G.cprod (qlist S (GlW.casI (la i))) (G.comp (la i) x) ∈ Submodule.span K (h '' {j | j ≠ i})) hx
      (fun hj x hx => ?_) (by simp) (fun x y hx hy => by rw [map_add, map_add]; exact Submodule.add_mem _ hx hy)
    by_cases hlj : la j = la i
    · obtain ⟨c', hc'⟩ := G.comp_top_of_mem (hh j) hx
      have e : G.comp (la i) x = c' • h j := by rw [← hlj]; exact hc'
      rw [e, map_smul, cprod_eig G (cas_hw G (hh j)) _, smul_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
    · rw [gen_kill G hW hS (hh j) (hhW j) (hh0 j) hμ (Dle_refl _) (fun _ => hlj) x hx]
      exact Submodule.zero_mem _
  have h1 := hQ _ hiK
  rw [(hh i).1, cprod_eig G (cas_hw G (hh i)) _] at h1
  have h2 := Submodule.smul_mem _ ((((qlist S (GlW.casI (la i))).map (fun c => (((GlW.casI (la i) - c : ℤ)) : K))).prod)⁻¹) h1
  rw [smul_smul, inv_mul_cancel₀ hs, one_smul] at h2
  exact hli.notMem_span_image (s := {j | j ≠ i}) (x := i) (by simp) h2
end Formalism.CountingSumsFrames.TO.GlX
