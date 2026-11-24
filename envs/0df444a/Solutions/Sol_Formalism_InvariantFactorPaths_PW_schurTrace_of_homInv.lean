-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.schurTrace_of_homInv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:50:01.792804+00:00
-- url     : https://prove2.me/submissions/132726cc-2f99-4091-8e7e-dc9f8ff08a7b

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementB
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_HomRelationHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_SchurTraceOfHomInv
import Theorems.Thm_Formalism_CountingSumsFrames_GlX_isWt_of_eig
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_E_diag_of_isWt
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_comp_top_of_mem
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
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_hom_trace_holds
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
open Finset Formalism.GM.DimensionMonotonicity
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution (h2 : HomInv) : SchurTrace := by
  intro K V _ _ _ _ n G W l hW hfd hfW hb la h hh hhW hh0 φ h0
  have hUW : G.gS {h} ≤ W := G.gS_le (by simpa using hhW) hW
  have : FiniteDimensional K (G.gS {h}) := Submodule.finiteDimensional_of_le hUW
  obtain ⟨c1, -, c3⟩ := h2 K (G.gS {h}) (G.gS {h}) n (res G _ (G.gS_stable {h})) (res G _ (G.gS_stable {h})) ⊤ l
    (fun _ _ _ _ => Submodule.mem_top)
    (fun μ ν x y hx hy _ hwx hwy c => hb μ ν x y (fun e => hx (Subtype.ext e)) (fun e => hy (Subtype.ext e))
      (hUW x.2) (hUW y.2) (congrArg Subtype.val hwx) (congrArg Subtype.val hwy) c)
    φ (fun _ => Submodule.mem_top) h0
  generalize InvOp (homAct (res G _ (G.gS_stable {h})).E (res G _ (G.gS_stable {h})).E) l (List.finRange n) φ = ψ
    at c1 c3 ⊢
  have hmem : h ∈ G.gS {h} := G.subset_gS {h} rfl
  have hwt : (res G _ (G.gS_stable {h})).IsWt la ⟨h, hmem⟩ := Subtype.ext hh.1
  have hwψ : (res G _ (G.gS_stable {h})).IsWt la (ψ ⟨h, hmem⟩) :=
    Formalism.CountingSumsFrames.GlX.isWt_of_eig _ (fun c => by
      rw [← c1, (res G _ (G.gS_stable {h})).E_diag_of_isWt hwt c, map_smul])
  obtain ⟨c, hc⟩ := G.comp_top_of_mem hh (ψ ⟨h, hmem⟩).2
  have hc' : ((ψ ⟨h, hmem⟩ : G.gS {h}) : V) = c • h := by
    rw [← hc]; exact (congrArg Subtype.val hwψ).symm
  have hle : G.gS {h} ≤ Submodule.map (G.gS {h}).subtype (LinearMap.ker (ψ - c • LinearMap.id)) := by
    apply G.gS_le
    · intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      refine ⟨⟨y, hmem⟩, ?_, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
      rw [sub_eq_zero]
      exact Subtype.ext hc'
    · rintro a b _ ⟨y, hy, rfl⟩
      refine ⟨(res G _ (G.gS_stable {h})).E a b y, ?_, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_apply] at hy ⊢
      rw [c1, ← map_smul, ← map_sub, hy, map_zero]
  have hψ : ψ = c • LinearMap.id := by
    ext x
    obtain ⟨y, hy, hyx⟩ := hle x.2
    have hyx' : y = x := Subtype.ext hyx
    subst hyx'
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply] at hy
    rw [sub_eq_zero.mp hy]
    rfl
  have htr : LinearMap.trace K _ (ψ - φ) = 0 := hom_trace_holds K (G.gS {h}) (Fin n) _ _ c3
  have : Nontrivial (G.gS {h}) := ⟨⟨⟨h, hmem⟩, 0, fun e => hh0 (congrArg Subtype.val e)⟩⟩
  have hfr : (Module.finrank K (G.gS {h}) : K) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := K) (M := G.gS {h})).ne'
  rw [map_sub, sub_eq_zero, hψ, map_smul, LinearMap.trace_id, smul_eq_mul] at htr
  rw [hψ, ← htr, mul_div_assoc, div_self hfr, mul_one]
end Formalism.InvariantFactorPaths.PW
