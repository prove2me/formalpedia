-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.projection_lattice_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:52:31.294048+00:00
-- url     : https://prove2.me/submissions/0c7591ba-29c4-40a6-be72-ac6df33fa690

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_WeightCompApply
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_FischerAdjointnessHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_OrthogonalIsomorphismHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_mem_perpS
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_span_isomorphism_holds
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_orthogonal_isomorphism_holds
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
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_fock_nondeg
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_PW_fock_add_left__c646ba94555b
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_PW_fock_add_right__407452ae58c2
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_PW_fock_symm__e96ddd2ea090
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
open Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r n : ℕ}
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution : ProjP := by
  intro p _ N r LL j Cs T hT
  set A := ⨆ la ∈ T, IsoC p LL j Cs la with hA
  set B := ⨆ mu, ⨆ (_ : mu ∉ T), IsoC p LL j Cs mu with hB
  have horth : ∀ la mu : Fin r → ℤ, la ∈ T → mu ∉ T →
      ∀ x ∈ IsoC p LL j Cs la, ∀ y ∈ IsoC p LL j Cs mu, fock p x y = 0 := by
    intro la mu hla hmu x hx y hy
    have hne : ∃ c ∈ Cs, la c ≠ mu c := by
      by_contra hcon
      push_neg at hcon
      exact hmu ((hT la mu hcon).mp hla)
    exact orthogonal_isomorphism_holds p N r LL j Cs la mu hne x hx y hy
  have hAB : A ≤ perpS B := by
    refine iSup₂_le fun la hla => ?_
    intro y hy
    rw [mem_perpS]
    intro x hx
    have hBle : B ≤ perpS (IsoC p LL j Cs la) := by
      refine iSup₂_le fun mu hmu => ?_
      intro z hz
      rw [mem_perpS]
      intro w hw
      exact horth la mu hla hmu w hw z hz
    have hx' := hBle hx
    rw [mem_perpS] at hx'
    rw [fock_symm']
    exact hx' y hy
  have hsup : A ⊔ B = ⊤ := by
    rw [eq_top_iff, ← span_isomorphism_holds p N r LL j Cs]
    refine iSup_le fun la => ?_
    by_cases hla : la ∈ T
    · exact le_sup_of_le_left (le_iSup₂_of_le la hla le_rfl)
    · exact le_sup_of_le_right (le_iSup₂_of_le la hla le_rfl)
  have hAB' : ∀ a ∈ A, ∀ b ∈ B, fock p a b = 0 := by
    intro a ha b hb
    have h1 := hAB ha
    rw [mem_perpS] at h1
    rw [fock_symm']
    exact h1 b hb
  have hcompl : IsCompl A B := by
    constructor
    · rw [Submodule.disjoint_def]
      intro x hxA hxB
      apply fock_nondeg x
      intro G
      have hG : G ∈ A ⊔ B := by
        rw [hsup]
        exact Submodule.mem_top
      obtain ⟨g1, hg1, g2, hg2, rfl⟩ := Submodule.mem_sup.mp hG
      rw [fock_add_right', fock_symm', hAB' g1 hg1 x hxB, hAB' x hxA g2 hg2, add_zero]
    · rw [codisjoint_iff, hsup]
  have hdec : ∀ H, ∃ h1 ∈ A, ∃ h2 ∈ B, H = h1 + h2 ∧ (A.subtype ∘ₗ A.projectionOnto B hcompl) H = h1 := by
    intro H
    have hH : H ∈ A ⊔ B := by
      rw [hsup]
      exact Submodule.mem_top
    obtain ⟨h1, hh1, h2, hh2, rfl⟩ := Submodule.mem_sup.mp hH
    have e1 : A.projectionOnto B hcompl h1 = ⟨h1, hh1⟩ :=
      Submodule.linearProjOfIsCompl_apply_left hcompl ⟨h1, hh1⟩
    have e2 : A.projectionOnto B hcompl h2 = 0 :=
      Submodule.linearProjOfIsCompl_apply_right hcompl ⟨h2, hh2⟩
    refine ⟨h1, hh1, h2, hh2, rfl, ?_⟩
    rw [LinearMap.comp_apply, map_add, e1, e2, add_zero]
    rfl
  refine ⟨A.subtype ∘ₗ A.projectionOnto B hcompl, ⟨?_, ?_, ?_⟩, ?_⟩
  · ext x
    simp only [LinearMap.comp_apply, Submodule.coe_subtype, Submodule.linearProjOfIsCompl_apply_left]
  · rw [LinearMap.range_comp, Submodule.linearProjOfIsCompl_range, Submodule.map_subtype_top]
  · rw [LinearMap.ker_comp, Submodule.ker_subtype, Submodule.comap_bot, Submodule.linearProjOfIsCompl_ker]
  · intro F G
    obtain ⟨f1, hf1, f2, hf2, rfl, hPF⟩ := hdec F
    obtain ⟨g1, hg1, g2, hg2, rfl, hPG⟩ := hdec G
    rw [hPF, hPG, fock_add_right', fock_add_left', hAB' f1 hf1 g2 hg2, fock_symm' f2 g1,
      hAB' g1 hg1 f2 hf2]
end Formalism.InvariantFactorPaths.PW
