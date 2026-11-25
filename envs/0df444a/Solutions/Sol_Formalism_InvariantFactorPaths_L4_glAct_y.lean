-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.glAct_y
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:28:50.362399+00:00
-- url     : https://prove2.me/submissions/f7eb9393-2a98-4ec5-9b6a-c6c0c5d6e01d

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_LatDefs
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_MulEarlyModP
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_DischargeHeightBound
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RestrictedLatticeDividedPower
import Theorems.Thm_Formalism_CountingSumsFrames_glAct_pol
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_glAct_pol
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_glAct_split
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
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_glAct_split
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_glRest_mem
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_ops_ycond
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
private theorem glAct_mem_yCond_r {N : ℕ} (LL : Letters N) (j : ℕ) (Mt : WithTop ℤ) (a b : Fin r) :
    ∀ x ∈ YCond p (r := r) LL j Mt, glAct p LL j a b x ∈ YCond p LL j Mt := by
  intro x hx
  have hle : YCond p (r := r) LL j Mt ≤ (YCond p LL j Mt).comap (glAct p LL j a b) := by
    unfold YCond
    exact sSup_le fun S hS y hy => le_sSup hS (hS.2 a b y hy)
  exact hle hx
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
theorem _root_.solution (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (c d : Fin r) :
    ∀ h ∈ Y p LL J M, glAct p LL (K + 1) c d h ∈ Y p LL J M := by
  intro h hh
  rw [Y, Submodule.mem_inf, Submodule.mem_iInf] at hh ⊢
  refine ⟨glAct_pol LL LL (K + 1) c d hh.1, fun k => ?_⟩
  have hk := hh.2 k
  by_cases hJ : J k ≤ K + 1
  · rw [glAct_split LL (J k) (K + 1) c d, LinearMap.add_apply]
    exact (YCond p LL (J k) (M k)).add_mem (glAct_mem_yCond_r LL (J k) (M k) c d h hk)
      (ops_ycond LL (J k) (M k) _ (glRest_mem LL (J k) (K + 1) hJ c d) h hk)
  · rw [yCond_of_K_succ_le LL (J k) (M k) (by omega)] at hk ⊢
    exact glAct_mem_yCond_r LL (K + 1) (M k) c d h hk
end Formalism.InvariantFactorPaths.L4
