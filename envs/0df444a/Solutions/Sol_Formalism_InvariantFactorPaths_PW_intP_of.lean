-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.intP_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:16:06.754179+00:00
-- url     : https://prove2.me/submissions/a5fd2fd2-2e82-49bc-9f6e-4630c22b1e5e

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_LatData
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementB
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_PolLeISupIsoW
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_isoW_eq_bot
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_pol_le_iSup_isoW
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_isoW_le_isoC
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
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_comp_eq_iff
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_exists_ext
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_polLatData_of
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
theorem _root_.solution (hT : TypeInt) (hB : LatBasisPol) : IntP := by
  classical
  intro p _ N r LL j Cs T P hsat hP F hF
  obtain ⟨hPP, hran, hker⟩ := hP
  have D := polLatData_of hB (p := p) (r := r) LL LL j (enumC Cs)
  obtain ⟨S, hS⟩ := D.finW
  choose Q hQ1 hQ2 hQ3 using hT p _ Cs.card (GAe p LL j (enumC Cs)) (Pol p r LL) _ LL.total D
  have key : ∀ x ∈ Pol p r LL,
      P x = ∑ μ ∈ S.filter (fun μ => ∃ la ∈ T, la ∘ enumC Cs = μ), Q μ x := by
    intro x hx
    refine Submodule.iSup_induction _
      (motive := fun x => P x = ∑ μ ∈ S.filter (fun μ => ∃ la ∈ T, la ∘ enumC Cs = μ), Q μ x)
      (pol_le_iSup_isoW LL LL j (enumC Cs) hx) ?_ ?_ ?_
    · intro ν x hx
      by_cases hν : ν ∈ S
      · obtain ⟨la, hla⟩ := exists_ext Cs ν
        have hxC : x ∈ IsoC p LL j Cs la := isoW_le_isoC LL LL j Cs la (by rw [hla]; exact hx)
        by_cases hf : ∃ la' ∈ T, la' ∘ enumC Cs = ν
        · obtain ⟨la', hla'T, hla'⟩ := hf
          have hlaT : la ∈ T := (hsat la la' ((comp_eq_iff Cs la la').mp (hla.trans hla'.symm))).mpr hla'T
          have hxr : x ∈ LinearMap.range P := by
            rw [hran]; exact Submodule.mem_iSup_of_mem la (Submodule.mem_iSup_of_mem hlaT hxC)
          have hPx : P x = x := by
            obtain ⟨y, rfl⟩ := hxr
            exact LinearMap.congr_fun hPP y
          rw [hPx, Finset.sum_eq_single ν]
          · exact (hQ1 ν x hx).symm
          · intro μ _ hne
            exact hQ2 μ ν hne.symm x hx
          · intro hn
            exact absurd (Finset.mem_filter.mpr ⟨hν, la', hla'T, hla'⟩) hn
        · have hlaT : la ∉ T := fun h => hf ⟨la, h, hla⟩
          have hxk : x ∈ LinearMap.ker P := by
            rw [hker]; exact Submodule.mem_iSup_of_mem la (Submodule.mem_iSup_of_mem hlaT hxC)
          rw [LinearMap.mem_ker.mp hxk]
          symm
          refine Finset.sum_eq_zero fun μ hμ => ?_
          refine hQ2 μ ν ?_ x hx
          rintro rfl
          exact hf (Finset.mem_filter.mp hμ).2
      · rw [isoW_eq_bot _ _ hS hν, Submodule.mem_bot] at hx
        subst hx
        simp
    · simp
    · intro x y hx hy
      rw [map_add, hx, hy, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun μ _ => (map_add _ _ _).symm
  have hFp : F ∈ Pol p r LL := hF.1
  have hFi : F ∈ (IntPol p (Fin N × Fin r)).toAddSubgroup := hF.2
  rw [key F hFp, Finset.smul_sum, ← Submodule.mem_toAddSubgroup]
  exact AddSubgroup.sum_mem _ fun μ _ => hQ3 μ F hFi hFp
end Formalism.InvariantFactorPaths.PW
