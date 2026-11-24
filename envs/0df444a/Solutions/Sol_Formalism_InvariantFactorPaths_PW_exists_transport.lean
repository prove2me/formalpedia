-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.exists_transport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:50:25.297323+00:00
-- url     : https://prove2.me/submissions/886e1436-db2e-4bb8-8690-6f033ca5b383

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementB
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_HomRelationHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInt
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_TypeInt
import Theorems.Thm_Formalism_CountingSumsFrames_GlX_exists_theta
import Theorems.Thm_Formalism_CountingSumsFrames_proj_exists
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_exists_hwmod
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_gS_le
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_gS_stable
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_graded_of
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_hw_in_gS
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_subset_gS
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
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open Finset Formalism.GM.DimensionMonotonicity Formalism.CountingSumsFrames
variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {n : ℕ}
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution (G : GlW K V n) {W : Submodule K V} (hW : G.Stable W) (hWf : G.FinW W) {la : Fin n → ℤ}
    {h h' : V} (hh : G.IsHW la h) (hh' : G.IsHW la h') (hhW : h ∈ W) (hh'W : h' ∈ W) (h0 : h ≠ 0) :
    ∃ θ : G.gS {h} →ₗ[K] V, (∀ a b x, θ ((res G _ (G.gS_stable {h})).E a b x) = G.E a b (θ x)) ∧
      ∀ m ∈ G.gS {h'}, ∃ y, θ y = m := by
  have hbot : G.Stable (⊥ : Submodule K V) := by
    intro a b y hy
    rw [Submodule.mem_bot] at hy ⊢
    rw [hy, map_zero]
  by_cases h0' : h' = 0
  · refine ⟨0, fun a b x => by simp, fun m hm => ⟨0, ?_⟩⟩
    have hm0 : m ∈ (⊥ : Submodule K V) := G.gS_le (by
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      rw [hw, h0']
      exact Submodule.zero_mem _) hbot hm
    rw [Submodule.mem_bot] at hm0
    rw [hm0, map_zero]
  have hUW : G.gS {h} ≤ W := G.gS_le (Set.singleton_subset_iff.mpr hhW) hW
  have hU'W : G.gS {h'} ≤ W := G.gS_le (Set.singleton_subset_iff.mpr hh'W) hW
  obtain ⟨S, hS⟩ := hWf
  by_cases hdis : G.gS {h} ⊓ G.gS {h'} = ⊥
  · have hind : iSupIndep (fun i : Bool => if i then G.gS {h'} else G.gS {h}) := by
      rw [iSupIndep_pair (i := true) (j := false) (by decide) (fun k => by cases k <;> simp), disjoint_iff]
      show G.gS {h'} ⊓ G.gS {h} = ⊥
      rw [inf_comm]
      exact hdis
    have hRW : ∀ i : Bool, (if i then G.gS {h'} else G.gS {h}) ≤ G.gS {h} ⊔ G.gS {h'} := by
      intro i
      cases i <;> simp
    have hWR : G.gS {h} ⊔ G.gS {h'} ≤ ⨆ i : Bool, (if i then G.gS {h'} else G.gS {h}) :=
      sup_le (le_iSup (fun i : Bool => if i then G.gS {h'} else G.gS {h}) false)
        (le_iSup (fun i : Bool => if i then G.gS {h'} else G.gS {h}) true)
    obtain ⟨π, hπ1, hπ2, hπ3⟩ := proj_exists (W := G.gS {h} ⊔ G.gS {h'})
      (fun i : Bool => if i then G.gS {h'} else G.gS {h}) hind hRW hWR
    have hEq : ∀ i, ∀ x ∈ G.gS {h} ⊔ G.gS {h'}, ∀ c d, π i (G.E c d x) = G.E c d (π i x) := by
      intro i x hx c d
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
      have hy' : G.E c d y ∈ G.gS {h} := G.gS_stable _ c d y hy
      have hz' : G.E c d z ∈ G.gS {h'} := G.gS_stable _ c d z hz
      simp only [map_add]
      cases i
      · rw [hπ2 false _ hy', hπ2 false _ hy, hπ3 false true (by decide) _ hz', hπ3 false true (by decide) _ hz,
          map_zero]
      · rw [hπ3 true false (by decide) _ hy', hπ3 true false (by decide) _ hy, hπ2 true _ hz', hπ2 true _ hz,
          map_zero]
    have hW' : G.Stable (G.gS {h} ⊔ G.gS {h'}) := by
      intro a b x hx
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
      rw [map_add]
      exact Submodule.add_mem _ (Submodule.mem_sup_left (G.gS_stable _ a b y hy))
        (Submodule.mem_sup_right (G.gS_stable _ a b z hz))
    have hWf' : G.FinW (G.gS {h} ⊔ G.gS {h'}) := ⟨S, fun x hx => hS x (sup_le hUW hU'W hx)⟩
    obtain ⟨θ₁, θ₁', hθ1, -, -, hθE', hinv⟩ := GlX.exists_theta G (W := G.gS {h} ⊔ G.gS {h'}) hW' hWf'
      (h := h') (h' := h) hh' hh (Submodule.mem_sup_right (G.subset_gS _ (Set.mem_singleton h')))
      (Submodule.mem_sup_left (G.subset_gS _ (Set.mem_singleton h))) h0' h0 (π true) (π false)
      (hπ1 true) (hπ2 true) (hEq true) (hπ1 false) (hπ2 false) (hEq false)
    refine ⟨θ₁' ∘ₗ (G.gS {h}).subtype, fun a b x => ?_, fun m hm => ⟨⟨θ₁ m, hθ1 m⟩, hinv m hm⟩⟩
    show θ₁' (G.E a b (x : V)) = G.E a b (θ₁' (x : V))
    exact hθE' _ (Submodule.mem_sup_left x.2) a b
  · have hI : G.Stable (G.gS {h} ⊓ G.gS {h'}) := by
      intro a b x hx
      rw [Submodule.mem_inf] at hx ⊢
      exact ⟨G.gS_stable _ a b x hx.1, G.gS_stable _ a b x hx.2⟩
    obtain ⟨v, hvI, hv0, μ, hvw, hvr⟩ := G.exists_hwmod (U := ⊥) (G.graded_of hI)
      (fun a b _ x hx => hI a b x hx) ⟨S, fun x hx => hS x (hUW (Submodule.mem_inf.mp hx).1)⟩
      (fun hle => hdis (le_bot_iff.mp hle))
    have hvHW : G.comp μ v = v ∧ ∀ a b, a < b → G.E a b v = 0 := ⟨hvw, fun a b hab => by
      have hq := hvr a b hab
      rwa [Submodule.mem_bot] at hq⟩
    have hv0' : v ≠ 0 := fun hq => hv0 (by rw [hq]; exact Submodule.zero_mem _)
    obtain ⟨-, c', hc'⟩ := G.hw_in_gS hh' hW ⟨S, hS⟩ hh'W (Submodule.mem_inf.mp hvI).2 hvHW hv0'
    have hc'0 : c' ≠ 0 := by
      rintro rfl
      apply hv0'
      rw [hc', zero_smul]
    have hmem : h' ∈ G.gS {h} := by
      have hq : h' = c'⁻¹ • v := by rw [hc', smul_smul, inv_mul_cancel₀ hc'0, one_smul]
      rw [hq]
      exact Submodule.smul_mem _ _ (Submodule.mem_inf.mp hvI).1
    have hle : G.gS {h'} ≤ G.gS {h} := G.gS_le (Set.singleton_subset_iff.mpr hmem) (G.gS_stable _)
    exact ⟨(G.gS {h}).subtype, fun a b x => rfl, fun m hm => ⟨⟨m, hle hm⟩, rfl⟩⟩
end Formalism.InvariantFactorPaths.PW
