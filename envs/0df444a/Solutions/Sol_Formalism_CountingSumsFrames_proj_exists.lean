-- Prove2me | solution 1 for Formalism.CountingSumsFrames.proj_exists
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:37:29.139842+00:00
-- url     : https://prove2.me/submissions/eaa5e98a-cde6-4d34-a0b6-707f6b7dd125

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount
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
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
namespace Formalism.CountingSumsFrames
theorem _root_.solution {W : Submodule K V} {ι : Type*} [DecidableEq ι] (R : ι → Submodule K V)
    (hind : iSupIndep R) (hRW : ∀ i, R i ≤ W) (hWR : W ≤ ⨆ i, R i) :
    ∃ π : ι → V →ₗ[K] V, (∀ i x, π i x ∈ R i) ∧ (∀ i, ∀ x ∈ R i, π i x = x) ∧
      (∀ i j, j ≠ i → ∀ x ∈ R j, π i x = 0) := by
  obtain ⟨D, hD⟩ := Submodule.exists_isCompl W
  have hc : ∀ i, IsCompl (R i) ((⨆ (j) (_ : j ≠ i), R j) ⊔ D) := by
    intro i
    constructor
    · rw [Submodule.disjoint_def]
      intro x hx hx2
      obtain ⟨y, hy, d, hd, rfl⟩ := Submodule.mem_sup.mp hx2
      have hyW : y ∈ W := (iSup_le fun j => iSup_le fun _ => hRW j) hy
      have hdW : d ∈ W := by
        have := W.sub_mem (hRW i hx) hyW
        rwa [add_sub_cancel_left] at this
      have hd0 : d = 0 := (Submodule.disjoint_def.mp hD.disjoint) d hdW hd
      subst hd0
      rw [add_zero] at hx ⊢
      exact (Submodule.disjoint_def.mp (hind i)) y hx hy
    · rw [codisjoint_iff, eq_top_iff]
      calc ⊤ = W ⊔ D := hD.codisjoint.eq_top.symm
        _ ≤ (⨆ j, R j) ⊔ D := sup_le_sup_right hWR D
        _ = R i ⊔ ((⨆ (j) (_ : j ≠ i), R j) ⊔ D) := by rw [iSup_split_single R i, sup_assoc]
  refine ⟨fun i => (R i).subtype ∘ₗ (R i).projectionOnto _ (hc i), fun i x => by simp,
    fun i x hx => ?_, fun i j hji x hx => ?_⟩
  · have := Submodule.projectionOnto_apply_left (hc i) ⟨x, hx⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply]
    rw [this]
  · have hxq : x ∈ (⨆ (j) (_ : j ≠ i), R j) ⊔ D :=
      Submodule.mem_sup_left (Submodule.mem_iSup_of_mem j (Submodule.mem_iSup_of_mem hji hx))
    have := Submodule.projectionOnto_apply_right (hc i) ⟨x, hxq⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply]
    rw [this]; rfl
end Formalism.CountingSumsFrames
