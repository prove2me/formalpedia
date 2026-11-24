-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.pol_le_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:58:35.020589+00:00
-- url     : https://prove2.me/submissions/cc981a58-d22d-438a-a3ca-33362f07ddd3

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementH
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_HighestVectorProjection
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_HighestVectorProjectionPos
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_supp_le_of_monomial
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_glAct_none
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_wt_none
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_glAct_one
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_wt_one
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_move_mem
import Theorems.Thm_Formalism_CountingSumsFrames_hwc_le_isoC
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
import Theorems.Thm_Formalism_GM_M_FB_glAct_one
import Theorems.Thm_Formalism_GM_M_FB_res_apply
import Theorems.Thm_Formalism_GM_M_FB_res_ext
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_last
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_last
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
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
attribute [local simp] Formalism.GM.QuotientRingDecomposition.E_apply
attribute [local simp] Formalism.GM.QuotientRingDecomposition.divQ_apply



set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (LL : Letters N) (j : ℕ) (hj : j ≤ 1) (hr : 1 ≤ r) :
    ∃ la : Fin r → ℤ, Pol p r LL ≤ IsoC p LL j univ la := by
  by_cases hex : ∃ i0 : Fin N, (i0 : ℕ) < j
  · obtain ⟨i0, hi0⟩ := hex
    have hj1 : j = 1 := by omega
    have h0 : (i0 : ℕ) = 0 := by omega
    subst hj1
    rcases Bool.eq_false_or_eq_true (LL.vec i0) with hv | hv
    ·
      refine ⟨fun c => if c = (⟨0, hr⟩ : Fin r) then (LL.deg i0 : ℤ) else 0, ?_⟩
      simp only [Formalism.GM.M.IsoC, Formalism.GM.M.Pol]
      refine le_sInf ?_
      rintro S ⟨hHS, hGS⟩
      apply supp_le_of_monomial
      intro m hm
      have hm' : ∀ i, ∑ c, m (i, c) = LL.deg i := hm
      have hbase : ∀ m : Fin N × Fin r →₀ ℕ, (∀ c, c ≠ (⟨0, hr⟩ : Fin r) → m (i0, c) = 0) →
          m (i0, ⟨0, hr⟩) = LL.deg i0 → monomial m (1 : ℚ_[p]) ∈ S := by
        intro m hz hd
        apply hHS
        simp only [Formalism.GM.M.HWC, Formalism.GM.M.WtSpC, Submodule.mem_inf, Submodule.mem_iInf,
          LinearMap.mem_ker]
        refine ⟨?_, ?_⟩
        · rw [MvPolynomial.mem_restrictSupport_iff]
          intro m2 hm2
          have hm3 := MvPolynomial.support_monomial_subset (Finset.mem_coe.mp hm2)
          rw [Finset.mem_singleton] at hm3
          subst hm3
          simp only [Set.mem_setOf_eq]
          intro c _
          rw [wt_one LL i0 h0 c, hv, if_pos rfl]
          by_cases hc : c = ⟨0, hr⟩
          · rw [if_pos hc, hc, hd]
          · rw [if_neg hc, hz c hc]
            simp
        · intro c d hcd
          have hd0 : d ≠ ⟨0, hr⟩ := by
            intro hd0
            have hlt := hcd.2.2
            rw [hd0, Fin.lt_def] at hlt
            exact Nat.not_lt_zero _ hlt
          rw [glAct_one LL i0 h0 c d, hv, if_pos rfl, pderiv_monomial, hz d hd0]
          simp
      have hst : ∀ a, ∀ x ∈ S, X (i0, a) * pderiv (i0, (⟨0, hr⟩ : Fin r)) x ∈ S := by
        intro a x hx
        have h1 := hGS a (Finset.mem_univ _) ⟨0, hr⟩ (Finset.mem_univ _) x hx
        rwa [glAct_one LL i0 h0, hv, if_pos rfl] at h1
      have hle : m (i0, ⟨0, hr⟩) ≤ LL.deg i0 := by
        rw [← hm' i0]
        exact Finset.single_le_sum (f := fun c => m (i0, c)) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ _)
      exact move_mem i0 ⟨0, hr⟩ (LL.deg i0) S hbase hst (LL.deg i0 - m (i0, ⟨0, hr⟩)) m
        (by omega) (hm' i0)
    ·
      refine ⟨fun c => -(if c = (⟨r - 1, by omega⟩ : Fin r) then (LL.deg i0 : ℤ) else 0), ?_⟩
      simp only [Formalism.GM.M.IsoC, Formalism.GM.M.Pol]
      refine le_sInf ?_
      rintro S ⟨hHS, hGS⟩
      apply supp_le_of_monomial
      intro m hm
      have hm' : ∀ i, ∑ c, m (i, c) = LL.deg i := hm
      have hbase : ∀ m : Fin N × Fin r →₀ ℕ,
          (∀ c, c ≠ (⟨r - 1, by omega⟩ : Fin r) → m (i0, c) = 0) →
          m (i0, ⟨r - 1, by omega⟩) = LL.deg i0 → monomial m (1 : ℚ_[p]) ∈ S := by
        intro m hz hd
        apply hHS
        simp only [Formalism.GM.M.HWC, Formalism.GM.M.WtSpC, Submodule.mem_inf, Submodule.mem_iInf,
          LinearMap.mem_ker]
        refine ⟨?_, ?_⟩
        · rw [MvPolynomial.mem_restrictSupport_iff]
          intro m2 hm2
          have hm3 := MvPolynomial.support_monomial_subset (Finset.mem_coe.mp hm2)
          rw [Finset.mem_singleton] at hm3
          subst hm3
          simp only [Set.mem_setOf_eq]
          intro c _
          rw [wt_one LL i0 h0 c, hv, if_neg Bool.false_ne_true]
          by_cases hc : c = ⟨r - 1, by omega⟩
          · rw [if_pos hc, hc, hd]
          · rw [if_neg hc, hz c hc]
            simp
        · intro c d hcd
          have hct : c ≠ ⟨r - 1, by omega⟩ := by
            intro hct
            have hlt := hcd.2.2
            rw [Fin.lt_def, hct] at hlt
            have hdr := d.isLt
            simp only at hlt
            omega
          rw [glAct_one LL i0 h0 c d, hv, if_neg Bool.false_ne_true, pderiv_monomial, hz c hct]
          simp
      have hst : ∀ a, ∀ x ∈ S, X (i0, a) * pderiv (i0, (⟨r - 1, by omega⟩ : Fin r)) x ∈ S := by
        intro a x hx
        have h1 := hGS ⟨r - 1, by omega⟩ (Finset.mem_univ _) a (Finset.mem_univ _) x hx
        rw [glAct_one LL i0 h0, hv, if_neg Bool.false_ne_true] at h1
        have h2 := S.neg_mem h1
        rwa [neg_neg] at h2
      have hle : m (i0, ⟨r - 1, by omega⟩) ≤ LL.deg i0 := by
        rw [← hm' i0]
        exact Finset.single_le_sum (f := fun c => m (i0, c)) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ _)
      exact move_mem i0 ⟨r - 1, by omega⟩ (LL.deg i0) S hbase hst
        (LL.deg i0 - m (i0, ⟨r - 1, by omega⟩)) m (by omega) (hm' i0)
  · push_neg at hex
    have hn : ∀ i : Fin N, ¬ (i : ℕ) < j := fun i => not_lt.mpr (hex i)
    refine ⟨0, fun F _ => ?_⟩
    refine Formalism.CountingSumsFrames.hwc_le_isoC (p := p) LL j 0 ?_
    simp only [Formalism.GM.M.HWC, Formalism.GM.M.WtSpC, Submodule.mem_inf, Submodule.mem_iInf,
      LinearMap.mem_ker, MvPolynomial.mem_restrictSupport_iff]
    refine ⟨fun m _ => ?_, fun c d _ => ?_⟩
    · simp only [Set.mem_setOf_eq]
      intro c _
      rw [wt_none LL j hn]
      rfl
    · simp [glAct_none LL j hn]
end Formalism.InvariantFactorPaths.L4
