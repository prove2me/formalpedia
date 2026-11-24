-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.GlX.eqExt_core
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:32:28.942728+00:00
-- url     : https://prove2.me/submissions/175587b7-1ba8-43f5-8709-2b6f5d37a2c8

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_CountingSumsFrames_TO_GlX_indep_hw
import Theorems.Thm_Formalism_CountingSumsFrames_TO_GlX_range_Lv
import Theorems.Thm_Formalism_CountingSumsFrames_TO_GlX_ker_le
import Theorems.Thm_Formalism_CountingSumsFrames_TO_GlX_tr_apply
import Theorems.Thm_Formalism_CountingSumsFrames_TO_proj_exists
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_gS_le
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
theorem _root_.solution {W : Submodule K V} (hW : G.Stable W) (hWf : G.FinW W) {ι : Type} [Fintype ι] [DecidableEq ι]
    (h g : ι → V) (la : ι → Fin r → ℤ) (hh : ∀ i, G.IsHW (la i) (h i)) (hhW : ∀ i, h i ∈ W)
    (hli : LinearIndependent K h) (hsp : W ≤ ⨆ i, G.gS {h i})
    (hg : ∀ i, G.IsHW (la i) (g i)) (hgW : ∀ i, g i ∈ W) :
    ∃ φ : V →ₗ[K] V, ∀ i c, φ (Lv G (h i) c) = Lv G (g i) c := by
  have h0 : ∀ i, h i ≠ 0 := fun i => hli.ne_zero i
  have hk : ∀ i, LinearMap.ker (Lv G (h i)) ≤ LinearMap.ker (Lv G (g i)) := fun i =>
    ker_le G hW hWf (hh i) (hg i) (hhW i) (hgW i) (h0 i)
  obtain ⟨S, hS⟩ := hWf
  have hind := indep_hw G hW hS h la hh hhW hli
  have hRW : ∀ i, G.gS {h i} ≤ W := fun i => G.gS_le (by simpa using hhW i) hW
  obtain ⟨π, hπ1, hπ2, hπ3⟩ := proj_exists (fun i => G.gS {h i}) hind hRW hsp
  have hπr : ∀ i x, π i x ∈ LinearMap.range (Lv G (h i)) := fun i x => by rw [range_Lv]; exact hπ1 i x
  refine ⟨∑ i, tr G (hk i) ∘ₗ (π i).codRestrict (LinearMap.range (Lv G (h i))) (hπr i), fun i c => ?_⟩
  have hmem : Lv G (h i) c ∈ G.gS {h i} := by rw [← range_Lv]; exact LinearMap.mem_range_self _ c
  rw [LinearMap.sum_apply, Finset.sum_eq_single i]
  · rw [LinearMap.comp_apply]
    have e : (π i).codRestrict (LinearMap.range (Lv G (h i))) (hπr i) (Lv G (h i) c) =
        ⟨Lv G (h i) c, LinearMap.mem_range_self _ c⟩ := by
      ext; exact hπ2 i _ hmem
    rw [e, tr_apply]
  · intro j _ hji
    rw [LinearMap.comp_apply]
    have e : (π j).codRestrict (LinearMap.range (Lv G (h j))) (hπr j) (Lv G (h i) c) = 0 := by
      ext; exact hπ3 j i (Ne.symm hji) _ hmem
    rw [e, map_zero]
  · intro hi; exact absurd (Finset.mem_univ i) hi
end Formalism.CountingSumsFrames.TO.GlX
