-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.typeInt_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:51:14.166203+00:00
-- url     : https://prove2.me/submissions/82bf1a11-1060-4fcb-b1bb-e0b1553d2142

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementB
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_HomRelationHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInt
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_TypeInt
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_comp_comm2
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_QQ_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_QQ_id
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_res_E_coe
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_res_comp_coe
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_res_pow_coe
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_IsoW_le
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_IsoW_le_iSup
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_hw_IsoW_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_equiv_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_exists_transport
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_QQ_int
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_gS_le
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_gS_stable
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
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution (hNat : InvNat) (hHom : HomInv) (hSchur : SchurTrace) : TypeInt := by
  intro p _ V _ _ n G W M l hD la
  by_cases hex : ∃ h, G.IsHW la h ∧ h ∈ W ∧ h ≠ 0
  · obtain ⟨h, hhw, hhW, h0⟩ := hex
    have hhw' : G.comp la h = h ∧ ∀ a b, a < b → G.E a b h = 0 := hhw
    have hUW : G.gS {h} ≤ W := G.gS_le (Set.singleton_subset_iff.mpr hhW) hD.stable
    obtain ⟨S, hS⟩ := hD.finW
    obtain ⟨k, b, hbM, hbi⟩ := hD.basis (G.gS {h}) hUW
    have hk : k ≠ 0 := by
      rintro rfl
      apply h0
      have h1 : (⟨h, G.subset_gS _ (Set.mem_singleton h)⟩ : G.gS {h}) = 0 := b.ext_elem (fun i => i.elim0)
      exact congrArg Subtype.val h1
    have hfr : (Module.finrank ℚ_[p] (G.gS {h}) : ℚ_[p]) = (k : ℚ_[p]) := by
      rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
    have hSch : ∀ φ : (G.gS {h}) →ₗ[ℚ_[p]] (G.gS {h}),
        (∀ c, homAct (res G (G.gS {h}) (G.gS_stable {h})).E (res G (G.gS {h}) (G.gS_stable {h})).E c c φ = 0) →
        InvOp (homAct (res G (G.gS {h}) (G.gS_stable {h})).E (res G (G.gS {h}) (G.gS_stable {h})).E) l (List.finRange n) φ =
          (LinearMap.trace ℚ_[p] _ φ / (k : ℚ_[p])) • LinearMap.id := fun φ hφ => by
      rw [hSchur ℚ_[p] V n G W l hD.stable hD.fd hD.finW hD.bound la h hhw hhW h0 φ hφ, hfr]
    have hS' : ∀ (x : G.gS {h}) (μ : Fin n → ℤ), μ ∉ S → (res G (G.gS {h}) (G.gS_stable {h})).comp μ x = 0 :=
      fun x μ hμ => Subtype.ext (by rw [res_comp_coe]; exact hS _ (hUW x.2) μ hμ)
    refine ⟨QQ (res G (G.gS {h}) (G.gS_stable {h})) G S l b, ?_, ?_, ?_⟩
    · intro x hx
      have hle : (⨆ v : {v : V // G.IsHW la v ∧ v ∈ W}, G.gS {(v : V)}) ≤
          LinearMap.eqLocus (QQ (res G (G.gS {h}) (G.gS_stable {h})) G S l b) LinearMap.id := by
        refine iSup_le fun v => ?_
        obtain ⟨θ, hθ, hsurj⟩ := exists_transport G hD.stable hD.finW hhw v.2.1 hhW v.2.2 h0
        intro m hm
        obtain ⟨y, rfl⟩ := hsurj m hm
        exact LinearMap.mem_eqLocus.mpr (QQ_id hNat (res G (G.gS {h}) (G.gS_stable {h})) G S l b hS' hSch hk θ hθ y)
      exact LinearMap.mem_eqLocus.mp (hle (IsoW_le_iSup G W la hx))
    · intro mu hmu x hx
      refine QQ_zero hHom (res G (G.gS {h}) (G.gS_stable {h})) G S l b (W := IsoW G W mu) (G.gS_stable _) ?_ ?_ hx
      · intro μ ν x' y hx0 hy0 hyI hxw hyw c
        have hxw' := congrArg Subtype.val hxw
        rw [res_comp_coe] at hxw'
        exact hD.bound μ ν (x' : V) y (fun h' => hx0 (Subtype.ext h')) hy0 (hUW x'.2) (IsoW_le G hD.stable mu hyI)
          hxw' hyw c
      · intro ψ hψ hψW
        refine equiv_zero G h ψ hψ ?_
        have hc : (res G (G.gS {h}) (G.gS_stable {h})).comp la ⟨h, G.subset_gS _ (Set.mem_singleton h)⟩ =
            ⟨h, G.subset_gS _ (Set.mem_singleton h)⟩ :=
          Subtype.ext (by rw [res_comp_coe]; exact hhw'.1)
        have hE : ∀ a b, a < b → (res G (G.gS {h}) (G.gS_stable {h})).E a b ⟨h, G.subset_gS _ (Set.mem_singleton h)⟩ = 0 :=
          fun a b hab => Subtype.ext (by rw [res_E_coe]; exact hhw'.2 a b hab)
        have hHW : G.comp la (ψ ⟨h, G.subset_gS _ (Set.mem_singleton h)⟩) = ψ ⟨h, G.subset_gS _ (Set.mem_singleton h)⟩ ∧
            ∀ a b, a < b → G.E a b (ψ ⟨h, G.subset_gS _ (Set.mem_singleton h)⟩) = 0 :=
          ⟨by rw [← comp_comm2 (res G (G.gS {h}) (G.gS_stable {h})) G ψ (fun c x => hψ c c x) la, hc],
            fun a b hab => by rw [← hψ, hE a b hab, map_zero]⟩
        exact hw_IsoW_zero G hD.stable hD.finW hmu hHW (hψW _)
    · intro m hm _
      refine QQ_int p (res G (G.gS {h}) (G.gS_stable {h})) G S l b (L := M.comap (G.gS {h}).subtype.toAddMonoidHom) hD.closed ?_ hD.div ?_
        hD.graded hbM hbi hm
      · intro a c hac j x hx
        show ((((j.factorial : ℚ_[p]))⁻¹ • (((res G (G.gS {h}) (G.gS_stable {h})).E a c ^ j) x) : G.gS {h}) : V) ∈ M
        rw [Submodule.coe_smul, res_pow_coe]
        exact hD.div a c hac j _ hx
      · intro μ x hx
        show (((res G (G.gS {h}) (G.gS_stable {h})).comp μ x : G.gS {h}) : V) ∈ M
        rw [res_comp_coe]
        exact hD.graded μ _ hx
  · push_neg at hex
    refine ⟨0, ?_, fun _ _ _ _ => rfl, fun m _ _ => by simp⟩
    intro x hx
    have hle : (⨆ v : {v : V // G.IsHW la v ∧ v ∈ W}, G.gS {(v : V)}) ≤ ⊥ := by
      refine iSup_le fun v => G.gS_le ?_ ?_
      · intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy, hex _ v.2.1 v.2.2]
        exact Submodule.zero_mem _
      · intro a b y hy
        rw [Submodule.mem_bot] at hy ⊢
        rw [hy, map_zero]
    have hx0 := hle (IsoW_le_iSup G W la hx)
    rw [Submodule.mem_bot] at hx0
    rw [hx0, map_zero]
end Formalism.InvariantFactorPaths.PW
