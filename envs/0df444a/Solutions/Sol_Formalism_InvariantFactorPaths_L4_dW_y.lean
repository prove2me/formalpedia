-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.dW_y
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:10:19.370882+00:00
-- url     : https://prove2.me/submissions/2ffc3175-8282-4601-b4cb-45faeec9aecb

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_LatDefs
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_MulEarlyModP
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_DischargeHeightBound
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RestrictedLatticeDividedPower
import Theorems.Thm_Formalism_GM_FockB_pderiv_mem
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
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_ops_ycond
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_yCond_setLast
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_ycond_pderiv
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


section
namespace Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.GM.DimensionMonotonicity Formalism.CountingSumsFrames Formalism.InvariantFactorPaths.PW MvPolynomial Finset
section LatM
variable {p : ℕ} [Fact p.Prime] {K : ℕ}
section general
variable {r : ℕ} [NeZero r]
private theorem yCond_of_K_succ_le (LL : Letters (K + 1)) (j : ℕ) (Mt : WithTop ℤ) (hj : K + 1 ≤ j) :
    YCond p (r := r) LL j Mt = YCond p LL (K + 1) Mt := by
  have hg : ∀ c d : Fin r, glAct p LL j c d = glAct p LL (K + 1) c d := by
    intro c d
    unfold glAct
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : (i : ℕ) < K + 1 := i.isLt
    have h2 : (i : ℕ) < j := by omega
    simp only [h1, h2, ↓reduceIte]
  have hw : ∀ m : Fin (K + 1) × Fin r →₀ ℕ, wt LL j 0 m = wt LL (K + 1) 0 m := by
    intro m
    unfold wt
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : (i : ℕ) < K + 1 := i.isLt
    have h2 : (i : ℕ) < j := by omega
    simp only [h1, h2, ↓reduceIte]
  unfold YCond GlStable
  simp_rw [hg, hw]
private theorem multiDeg_setLast_pred_of_add_single (LL : Letters (K + 1)) (o : ℕ) (a : Fin r) (m : Fin (K + 1) × Fin r →₀ ℕ)
    (hm : MultiDeg (setLast LL o) (m + Finsupp.single (Fin.last K, a) 1)) :
    MultiDeg (setLast LL (o - 1)) m := by
  intro i
  have h := hm i
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Finsupp.single_apply, Prod.mk.injEq] at h
  by_cases hi : i = Fin.last K
  · subst hi
    simp [setLast] at h ⊢
    omega
  · have hi' : Fin.last K ≠ i := Ne.symm hi
    simp [setLast, hi, hi'] at h ⊢
    exact h
end general
section larger
variable {s : ℕ}
end larger
end LatM
end Formalism.InvariantFactorPaths.L4
end

set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.GM.DimensionMonotonicity Formalism.CountingSumsFrames Formalism.InvariantFactorPaths.PW MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {K : ℕ}
variable {r : ℕ} [NeZero r]
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (LL : Letters (K + 1)) (hv : LL.vec (Fin.last K) = true) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
    (a : Fin r) (o : ℕ) : ∀ h ∈ Y p (setLast LL o) J M, dW p K a h ∈ Y p (setLast LL (o - 1)) J M := by
  intro h hh
  rw [Y, Submodule.mem_inf, Submodule.mem_iInf] at hh ⊢
  refine ⟨?_, fun k => ?_⟩
  · have hP := hh.1
    simp only [Pol, MvPolynomial.mem_restrictSupport_iff] at hP ⊢
    intro m hm
    have hm' : coeff m (pderiv (Fin.last K, a) h) ≠ 0 := mem_support_iff.1 hm
    rw [coeff_pderiv] at hm'
    have hs : m + Finsupp.single (Fin.last K, a) 1 ∈ h.support := mem_support_iff.2 (left_ne_zero_of_mul hm')
    exact multiDeg_setLast_pred_of_add_single LL o a m (hP hs)
  · have hk := hh.2 k
    rw [yCond_setLast] at hk ⊢
    by_cases hJ : J k ≤ K
    · exact ops_ycond LL (J k) (M k) (dW p K a) (FockB.pderiv_mem (by simp; omega)) h hk
    · rw [yCond_of_K_succ_le LL (J k) (M k) (by omega)] at hk ⊢
      exact ycond_pderiv LL hv (M k) a h hk
end Formalism.InvariantFactorPaths.L4
