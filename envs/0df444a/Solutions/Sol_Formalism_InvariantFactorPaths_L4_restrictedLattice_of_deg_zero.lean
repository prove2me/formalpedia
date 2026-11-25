-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.restrictedLattice_of_deg_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:00:53.661403+00:00
-- url     : https://prove2.me/submissions/d58cb453-ffa3-419f-b7e4-03bed3130aa7

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_LatDefs
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_MulEarlyModP
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_DischargeHeightBound
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RestrictedLatticeDividedPower
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_mem_restrictedLattice_of_mem
import Theorems.Thm_Formalism_CountingSumsFrames_glAct_pol
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_glAct_pol
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
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_glAct_succ
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_wt_succ
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_yCond_setLast
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
private theorem pderiv_last_eq_zero_of_mem_pol_setLast_zero (LL : Letters (K + 1)) (d : Fin r) (y : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p])
    (hP : y ∈ Pol p r (setLast LL 0)) : pderiv (Fin.last K, d) y = 0 := by
  rw [Pol, MvPolynomial.mem_restrictSupport_iff] at hP
  ext m
  rw [coeff_pderiv, coeff_zero]
  have h0 : coeff (m + Finsupp.single (Fin.last K, d) 1) y = 0 := by
    by_contra hne
    have hm := hP (mem_support_iff.2 hne) (Fin.last K)
    have hle : (m + Finsupp.single (Fin.last K, d) 1 : Fin (K + 1) × Fin r →₀ ℕ) (Fin.last K, d) ≤
        ∑ c, (m + Finsupp.single (Fin.last K, d) 1 : Fin (K + 1) × Fin r →₀ ℕ) (Fin.last K, c) :=
      Finset.single_le_sum
        (f := fun c => (m + Finsupp.single (Fin.last K, d) 1 : Fin (K + 1) × Fin r →₀ ℕ) (Fin.last K, c))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ d)
    rw [hm] at hle
    simp [setLast] at hle
  rw [h0, zero_mul]
private theorem mem_yCond_succ_of_mem_pol_setLast_zero (LL : Letters (K + 1)) (hv : LL.vec (Fin.last K) = true) (Mt : WithTop ℤ)
    (y : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (hy : y ∈ YCond p LL K Mt)
    (hP : y ∈ Pol p r (setLast LL 0)) : y ∈ YCond p LL (K + 1) Mt := by
  have hR : YCond p (r := r) LL K Mt ≤
      MvPolynomial.restrictSupport ℚ_[p] {m | ((wt LL K 0 m : ℤ) : WithTop ℤ) ≤ Mt} := by
    unfold YCond
    exact sSup_le fun S hS => hS.1
  have h1 : YCond p LL K Mt ⊓ Pol p r (setLast LL 0) ≤
      MvPolynomial.restrictSupport ℚ_[p] {m | ((wt LL (K + 1) 0 m : ℤ) : WithTop ℤ) ≤ Mt} := by
    intro z hz
    obtain ⟨hz1, hz2⟩ := Submodule.mem_inf.1 hz
    have hz1' := hR hz1
    rw [Pol, MvPolynomial.mem_restrictSupport_iff] at hz2
    rw [MvPolynomial.mem_restrictSupport_iff] at hz1' ⊢
    intro m hm
    have hw := hz1' hm
    have hd := hz2 hm (Fin.last K)
    have h0 : m (Fin.last K, 0) = 0 := by
      simp [setLast] at hd
      exact hd 0
    show ((wt LL (K + 1) 0 m : ℤ) : WithTop ℤ) ≤ Mt
    rw [wt_succ LL hv, h0]
    simpa using hw
  have h2 : GlStable p LL (K + 1) (YCond p LL K Mt ⊓ Pol p r (setLast LL 0)) := by
    intro c d z hz
    obtain ⟨hz1, hz2⟩ := Submodule.mem_inf.1 hz
    rw [glAct_succ LL hv, pderiv_last_eq_zero_of_mem_pol_setLast_zero LL d z hz2, mul_zero, add_zero]
    exact Submodule.mem_inf.2 ⟨glAct_mem_yCond_r LL K Mt c d z hz1, glAct_pol LL (setLast LL 0) K c d hz2⟩
  have hS : YCond p LL K Mt ⊓ Pol p r (setLast LL 0) ≤ YCond p LL (K + 1) Mt := le_sSup ⟨h1, h2⟩
  exact hS (Submodule.mem_inf.2 ⟨hy, hP⟩)
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
theorem _root_.solution (LL : Letters (K + 1)) (hv : LL.vec (Fin.last K) = true) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p])
    (hx : x ∈ XSp p (setLast LL 0) J M ρ) (hi : x ∈ IntPol p (Fin (K + 1) × Fin r)) : x ∈ M2 p LL J M ρ := by
  have hfix : initPart (Fin.last K, ρ) 0 x = x := by
    have hF : x ∈ FreeOf p (Fin.last K, ρ) := by
      simp only [XSp, Submodule.mem_inf] at hx
      exact hx.1.2
    rw [FreeOf, MvPolynomial.mem_restrictSupport_iff] at hF
    ext m
    rw [coeff_initPart]
    split_ifs with hm
    · rfl
    · by_contra hne
      exact hm (hF (mem_support_iff.2 (Ne.symm hne)))
  rw [← hfix]
  refine mem_restrictedLattice_of_mem LL J M ρ 0 x ?_ hi
  simp only [XSp, Submodule.mem_inf, Submodule.mem_iInf] at hx
  obtain ⟨⟨hP, _⟩, hk⟩ := hx
  rw [Y, Submodule.mem_inf, Submodule.mem_iInf]
  refine ⟨hP, fun k => ?_⟩
  have hk' := hk k
  rw [yCond_setLast]
  by_cases hJ : K + 1 ≤ J k
  · rw [if_pos hJ, Submodule.mem_inf, yCond_setLast] at hk'
    rw [yCond_of_K_succ_le LL (J k) (M k) hJ]
    exact mem_yCond_succ_of_mem_pol_setLast_zero LL hv (M k) x hk'.1 hP
  · rw [if_neg hJ, yCond_setLast] at hk'
    exact hk'
end Formalism.InvariantFactorPaths.L4
