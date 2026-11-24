-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.GlX.eqExt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:39:49.760462+00:00
-- url     : https://prove2.me/submissions/8610be7b-b0ca-4349-8e18-893efc72027c

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_CountingSumsFrames_TO_GlX_E_Lv
import Theorems.Thm_Formalism_CountingSumsFrames_TO_GlX_range_Lv
import Theorems.Thm_Formalism_CountingSumsFrames_TO_GlX_ker_le
import Theorems.Thm_Formalism_CountingSumsFrames_TO_GlX_Lv_single_nil
import Theorems.Thm_Formalism_CountingSumsFrames_TO_GlX_Lv_zero
import Theorems.Thm_Formalism_CountingSumsFrames_TO_GlX_eqExt_core
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
    ∃ φ : V →ₗ[K] V, (∀ i, φ (h i) = g i) ∧ (∀ x ∈ W, ∀ a b, φ (G.E a b x) = G.E a b (φ x)) ∧
      (∀ x ∈ W, φ x ∈ W) ∧ (∀ i, ∀ x ∈ G.gS {h i}, φ x ∈ G.gS {g i}) ∧
      (∀ i, g i ≠ 0 → ∀ x ∈ G.gS {h i}, φ x = 0 → x = 0) ∧
      (∀ i, g i = h i → ∀ x ∈ G.gS {h i}, φ x = x) ∧ (∀ i, g i = 0 → ∀ x ∈ G.gS {h i}, φ x = 0) := by
  obtain ⟨φ, hφ⟩ := eqExt_core G hW hWf h g la hh hhW hli hsp hg hgW
  have hrep : ∀ i, ∀ x ∈ G.gS {h i}, ∃ c, x = Lv G (h i) c := by
    intro i x hx
    rw [← range_Lv] at hx
    obtain ⟨c, rfl⟩ := hx
    exact ⟨c, rfl⟩
  have hgS : ∀ i c, Lv G (g i) c ∈ G.gS {g i} := fun i c => by
    rw [← range_Lv]; exact LinearMap.mem_range_self _ c
  refine ⟨φ, fun i => ?_, fun x hx a b => ?_, fun x hx => ?_, fun i x hx => ?_, fun i hgi x hx hx0 => ?_,
    fun i hgi x hx => ?_, fun i hgi x hx => ?_⟩
  · have := hφ i (Finsupp.single [] 1)
    rwa [Lv_single_nil, Lv_single_nil] at this
  · refine Submodule.iSup_induction (fun i => G.gS {h i}) (motive := fun x => φ (G.E a b x) = G.E a b (φ x))
      (hsp hx) (fun j y hy => ?_) (by simp) (fun x y hx hy => by simp only [map_add, hx, hy])
    obtain ⟨c, rfl⟩ := hrep j y hy
    rw [E_Lv, hφ, hφ, E_Lv]
  · refine Submodule.iSup_induction (fun i => G.gS {h i}) (motive := fun x => φ x ∈ W)
      (hsp hx) (fun j y hy => ?_) (by simp) (fun x y hx hy => by rw [map_add]; exact W.add_mem hx hy)
    obtain ⟨c, rfl⟩ := hrep j y hy
    rw [hφ]
    exact (G.gS_le (by simpa using hgW j) hW) (hgS j c)
  · obtain ⟨c, rfl⟩ := hrep i x hx
    rw [hφ]; exact hgS i c
  · obtain ⟨c, rfl⟩ := hrep i x hx
    rw [hφ] at hx0
    exact LinearMap.mem_ker.mp (ker_le G hW hWf (hg i) (hh i) (hgW i) (hhW i) hgi (LinearMap.mem_ker.mpr hx0))
  · obtain ⟨c, rfl⟩ := hrep i x hx
    rw [hφ, hgi]
  · obtain ⟨c, rfl⟩ := hrep i x hx
    rw [hφ, hgi, Lv_zero]
end Formalism.CountingSumsFrames.TO.GlX
