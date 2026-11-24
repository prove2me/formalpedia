-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.weylInt_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:35:25.76087+00:00
-- url     : https://prove2.me/submissions/90741de8-1353-4210-921a-e9c4e4a961a2

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_SchurTraceOfHomInv
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInv
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInt
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_WeylInt
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_wl_pow_coe
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_wl_iso_le
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_wl_iso_le_iSup
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_wl_comp_hw
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_wl_transport
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_wl_key
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_subset_deltaLat
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_deltaLat_closed
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_deltaLat_div
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_bot_stable
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_gS_le
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_gS_stable
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_graded_of
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
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_glRel_of
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_hom_divided_holds
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_hom_relation_holds
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_invariant_integral_holds
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
theorem _root_.solution (hNat : InvNat) (hSchur : SchurTrace) : WeylInt := by
  intro p _ V _ _ n G W M l D la x hx hxM
  by_cases hex : ∃ h, G.IsHW la h ∧ h ∈ W ∧ h ≠ 0
  swap
  · push Not at hex
    have hbot : IsoW G W la ≤ ⊥ := G.gS_le (fun v hv => by
      rw [SetLike.mem_coe, Submodule.mem_bot]; exact hex v hv.1 hv.2) G.bot_stable
    rw [(Submodule.mem_bot _).mp (hbot hx), smul_zero]
    exact AddSubgroup.zero_mem _
  obtain ⟨h, hh, hhW, h0⟩ := hex
  have hUW : G.gS {h} ≤ W := G.gS_le (by simpa using hhW) D.stable
  have := D.fd
  have : FiniteDimensional ℚ_[p] (G.gS {h}) := Submodule.finiteDimensional_of_le hUW
  have hmem : h ∈ G.gS {h} := G.subset_gS {h} rfl
  have : Nontrivial (G.gS {h}) := ⟨⟨⟨h, hmem⟩, 0, fun e => h0 (congrArg Subtype.val e)⟩⟩
  have hfr : (Module.finrank ℚ_[p] (G.gS {h}) : ℚ_[p]) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ_[p]) (M := G.gS {h})).ne'
  set Δ := DeltaLat p G {h | G.IsHW la h ∧ h ∈ W ∧ h ∈ M} with hΔ
  have hΔZ : ZpClosed p Δ := deltaLat_closed p G _
  have hΔD : DivStable G.E Δ := deltaLat_div p G _

  have hid : ∀ z : IsoW G W la,
      InvOp (homAct (res G (IsoW G W la) (wl_iso_stable G W la)).E G.E) l (List.finRange n) (topC G W la) z =
        ((Module.finrank ℚ_[p] (G.gS {h}) : ℚ_[p]))⁻¹ • (z : V) := by
    have hle : (⨆ v : {v : V // G.IsHW la v ∧ v ∈ W}, G.gS {(v : V)}) ≤
        Submodule.map (IsoW G W la).subtype (LinearMap.eqLocus
          (InvOp (homAct (res G (IsoW G W la) (wl_iso_stable G W la)).E G.E) l (List.finRange n) (topC G W la))
          (((Module.finrank ℚ_[p] (G.gS {h}) : ℚ_[p]))⁻¹ • (IsoW G W la).subtype)) := by
      refine iSup_le fun v m hm => ?_
      obtain ⟨θ, hθ, hθm, hsur⟩ := wl_transport G D.stable D.finW hh v.2.1 hhW v.2.2 h0
      have hvY : G.gS {(v : V)} ≤ IsoW G W la :=
        G.gS_le (by
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          subst hy
          exact G.subset_gS _ v.2) (G.gS_stable _)
      obtain ⟨y, rfl⟩ := hsur m hm
      exact ⟨⟨θ y, hvY (hθm y)⟩, wl_key hNat G W la l hh h0
        (fun φ hφ => hSchur ℚ_[p] V n G W l D.stable D.fd D.finW D.bound la h hh hhW h0 φ hφ) θ hθ
        (fun y => hvY (hθm y)) y, rfl⟩
    intro z
    obtain ⟨z', hz', hzz⟩ := hle (wl_iso_le_iSup G W la z.2)
    have : z' = z := Subtype.ext hzz
    rw [← this]
    exact hz'

  have hLd : DivStable (res G (IsoW G W la) (wl_iso_stable G W la)).E (M.comap (IsoW G W la).subtype.toAddMonoidHom) := by
    intro a b hab j y hy
    show ((((j.factorial : ℚ_[p]))⁻¹ • ((res G (IsoW G W la) (wl_iso_stable G W la)).E a b ^ j) y : IsoW G W la) : V) ∈ M
    rw [Submodule.coe_smul, wl_pow_coe]
    exact D.div a b hab j _ hy
  obtain ⟨hHZ, hHD⟩ := hom_divided_holds p (IsoW G W la) V (Fin n) (res G (IsoW G W la) (wl_iso_stable G W la)).E G.E
    (M.comap (IsoW G W la).subtype.toAddMonoidHom) Δ hΔZ hLd hΔD
  have hrel := hom_relation_holds ℚ_[p] (IsoW G W la) V (Fin n) (res G (IsoW G W la) (wl_iso_stable G W la)).E G.E
    (glRel_of (res G (IsoW G W la) (wl_iso_stable G W la))) (glRel_of G)
  have hφ : topC G W la ∈ HomLat (K := ℚ_[p]) (M.comap (IsoW G W la).subtype.toAddMonoidHom) Δ := by
    intro y hy
    exact subset_deltaLat p G _ ⟨wl_comp_hw G W la y.2,
      G.graded_of D.stable la _ (wl_iso_le G D.stable la y.2), D.graded la _ hy⟩
  have h2 := invariant_integral_holds p _ (Fin n) _ hrel _ hHZ hHD l (List.finRange n) (List.nodup_finRange n) _ hφ
  rw [List.length_finRange] at h2
  have h3 := h2 ⟨x, hx⟩ hxM
  rw [LinearMap.smul_apply, hid] at h3
  have h4 := hΔZ (Module.finrank ℚ_[p] (G.gS {h}) : ℚ_[p])
    (by simpa using Padic.norm_int_le_one (p := p) (Module.finrank ℚ_[p] (G.gS {h}) : ℤ)) _ h3
  rwa [smul_comm, smul_smul (Module.finrank ℚ_[p] (G.gS {h}) : ℚ_[p]), mul_inv_cancel₀ hfr, one_smul] at h4
end Formalism.InvariantFactorPaths.PW
