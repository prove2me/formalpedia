-- Prove2me | solution 1 for Formalism.CountingSumsFrames.GlX.exists_theta
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:30:32.335218+00:00
-- url     : https://prove2.me/submissions/b6b32923-8487-4a3a-b902-0486780c4a8d

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount
import Theorems.Thm_Formalism_CountingSumsFrames_GlX_range_Lv
import Theorems.Thm_Formalism_CountingSumsFrames_GlX_ker_le
import Theorems.Thm_Formalism_CountingSumsFrames_GlX_tr_E
import Theorems.Thm_Formalism_CountingSumsFrames_GlX_tr_tr
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_gS_stable
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
open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M
namespace Formalism.CountingSumsFrames
namespace GlX
theorem _root_.solution {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)
    {W : Submodule K V} (hW : G.Stable W) (hWf : G.FinW W) {la : Fin r → ℤ} {h h' : V}
    (hh : G.IsHW la h) (hh' : G.IsHW la h') (hhW : h ∈ W) (hh'W : h' ∈ W) (h0 : h ≠ 0) (h0' : h' ≠ 0)
    (π π' : V →ₗ[K] V) (h1 : ∀ x, π x ∈ G.gS {h}) (h2 : ∀ x ∈ G.gS {h}, π x = x)
    (hE : ∀ x ∈ W, ∀ c d, π (G.E c d x) = G.E c d (π x))
    (h1' : ∀ x, π' x ∈ G.gS {h'}) (h2' : ∀ x ∈ G.gS {h'}, π' x = x)
    (hE' : ∀ x ∈ W, ∀ c d, π' (G.E c d x) = G.E c d (π' x)) :
    ∃ θ θ' : V →ₗ[K] V, (∀ x, θ x ∈ G.gS {h'}) ∧ (∀ x ∈ W, ∀ c d, θ (G.E c d x) = G.E c d (θ x)) ∧
      (∀ x, θ' x ∈ G.gS {h}) ∧ (∀ x ∈ W, ∀ c d, θ' (G.E c d x) = G.E c d (θ' x)) ∧
      (∀ x ∈ G.gS {h}, θ' (θ x) = x) := by
  have hk := GlX.ker_le G hW hWf hh hh' hhW hh'W h0
  have hk' := GlX.ker_le G hW hWf hh' hh hh'W hhW h0'
  let ρ : V →ₗ[K] LinearMap.range (GlX.Lv G h) := π.codRestrict _ (fun x => by rw [GlX.range_Lv]; exact h1 x)
  let ρ' : V →ₗ[K] LinearMap.range (GlX.Lv G h') := π'.codRestrict _ (fun x => by rw [GlX.range_Lv]; exact h1' x)
  have hρ : ∀ x, ((ρ x : LinearMap.range (GlX.Lv G h)) : V) = π x := fun x => rfl
  have hρ' : ∀ x, ((ρ' x : LinearMap.range (GlX.Lv G h')) : V) = π' x := fun x => rfl
  refine ⟨GlX.tr G hk ∘ₗ ρ, GlX.tr G hk' ∘ₗ ρ', fun x => ?_, fun x hx c d => ?_, fun x => ?_, fun x hx c d => ?_,
    fun x hx => ?_⟩
  · rw [← GlX.range_Lv]; exact GlX.tr_mem G hk _
  · have hy : G.E c d (ρ x) ∈ LinearMap.range (GlX.Lv G h) :=
      (GlX.range_Lv G h).ge (G.gS_stable _ c d _ (h1 x))
    have e : ρ (G.E c d x) = ⟨G.E c d (ρ x), hy⟩ := Subtype.ext (hE x hx c d)
    simp only [LinearMap.comp_apply]
    rw [e, GlX.tr_E]
  · rw [← GlX.range_Lv]; exact GlX.tr_mem G hk' _
  · have hy : G.E c d (ρ' x) ∈ LinearMap.range (GlX.Lv G h') :=
      (GlX.range_Lv G h').ge (G.gS_stable _ c d _ (h1' x))
    have e : ρ' (G.E c d x) = ⟨G.E c d (ρ' x), hy⟩ := Subtype.ext (hE' x hx c d)
    simp only [LinearMap.comp_apply]
    rw [e, GlX.tr_E]
  · simp only [LinearMap.comp_apply]
    have hm : GlX.tr G hk (ρ x) ∈ G.gS {h'} := by rw [← GlX.range_Lv]; exact GlX.tr_mem G hk _
    have e : ρ' (GlX.tr G hk (ρ x)) = ⟨GlX.tr G hk (ρ x), GlX.tr_mem G hk _⟩ := Subtype.ext (h2' _ hm)
    rw [e, GlX.tr_tr G hk hk', hρ, h2 x hx]
end GlX
end Formalism.CountingSumsFrames
