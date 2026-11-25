-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.MC.gamma_zero_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:18:21.918467+00:00
-- url     : https://prove2.me/submissions/a6a431ad-48cb-4ff2-9a28-e31c259c8531

import Definitions.Def_Formalism_ThetaLogCoordinates_PartnerMeanCoordinates_TheoremMXB
import Definitions.Def_Formalism_ThetaLogCoordinates_PartnerMeanCoordinates_PartnerMeanProofs_GammaZeroIntegral
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_snoc_deg_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_snoc_deg_last
import Theorems.Thm_Formalism_GM_GammaExpansion_IsPD_mul
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
import Theorems.Thm_Formalism_GM_extendMapsTo
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_mul
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IVP_mul
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IsIntP_mul
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_deg_le_total
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_intPol_coeff
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_norm_K
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_norm_sum_le_bound
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_vW_ge
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_v_prod
import Theorems.Thm_P2M_Formalism_GM_gammaIntegralityLemmas_fock_def__dcd241737a4a
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
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.MC
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.DimensionMonotonicity Formalism.CountingSumsFrames Formalism.CountingSumsFrames.TO Formalism.InvariantFactorPaths.OddLevelGainBounds.TB MvPolynomial Finset
namespace Formalism.InvariantFactorPaths.MC
theorem _root_.solution {p : ℕ} [Fact p.Prime] (K r : ℕ) (LLw : Letters (K + 1)) (ρ : Fin r) (n a : ℕ) (κ : ℝ)
    (hS : LLw.total ≤ n) (hn : n ≤ a) (h4 : (K + 2) * (r * Nat.log p a) ≤ ⌈κ⌉₊)
    (f f' : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (hf : f ∈ PolZ p r LLw) (hf' : f' ∈ PolZ p r LLw) :
    ‖(p : ℚ_[p]) ^ ⌈κ⌉₊ * (fock p (freeze p LLw ρ n f) (freeze p LLw ρ n f') /
      ((((n - LLw.total).factorial * LLw.total.factorial : ℕ) : ℚ_[p]) *
        ∏ i, ((LLw.deg i).factorial : ℚ_[p])))‖ ≤ 1 := by
  classical
  have hr : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr (fun h => by subst h; exact ρ.elim0)
  obtain ⟨hfP, hfI⟩ := Submodule.mem_inf.mp hf
  obtain ⟨hfP', hfI'⟩ := Submodule.mem_inf.mp hf'
  obtain ⟨hFP, -, hFI⟩ := Formalism.GM.extendMapsTo p (K + 1) r LLw ρ n hS f hfP
  obtain ⟨-, -, hFI'⟩ := Formalism.GM.extendMapsTo p (K + 1) r LLw ρ n hS f' hfP'
  set F := freeze p LLw ρ n f with hF
  set F' := freeze p LLw ρ n f' with hF'
  have hc := gammaIntegralityLemmas.intPol_coeff F (hFI hfI)
  have hc' := gammaIntegralityLemmas.intPol_coeff F' (hFI' hfI')
  set Den : ℕ := ((n - LLw.total).factorial * LLw.total.factorial) * ∏ i, (LLw.deg i).factorial with hDen
  have hDen0 : Den ≠ 0 := by
    rw [hDen]
    exact Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.factorial_pos _).ne' (Nat.factorial_pos _).ne')
      (Finset.prod_ne_zero_iff.mpr fun i _ => (Nat.factorial_pos _).ne')
  have hDcast : ((((n - LLw.total).factorial * LLw.total.factorial : ℕ) : ℚ_[p]) *
        ∏ i, ((LLw.deg i).factorial : ℚ_[p])) = (Den : ℚ_[p]) := by
    rw [hDen]; push_cast; ring
  rw [hDcast, gammaIntegralityLemmas.fock_def', Finset.sum_div, Finset.mul_sum]
  refine gammaIntegralityLemmas.norm_sum_le_bound _ _ 1 zero_le_one ?_
  intro m hm
  have hmd : MultiDeg (LLw.snoc n) m := by
    rw [Pol, mem_restrictSupport_iff] at hFP
    exact hFP (Finset.mem_coe.mpr hm)
  set Num : ℕ := ∏ v : Fin (K + 1 + 1) × Fin r, (m v).factorial with hNum
  have hNum0 : Num ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => (Nat.factorial_pos _).ne'
  have hwf : gammaIntegralityLemmas.wf (p := p) m = (Num : ℚ_[p]) := by
    rw [hNum, gammaIntegralityLemmas.wf]; push_cast; rfl
  rw [hwf]
  have hδ : ∀ i, gammaIntegralityLemmas.δv m i = (LLw.snoc n).deg i := fun i => hmd i
  have hT : ∀ i, gammaIntegralityLemmas.δv m i ≤ a := by
    intro i
    rw [hδ]
    refine Fin.lastCases ?_ (fun i => ?_) i
    · rw [FrozenVariableComponents.snoc_deg_last]; exact hn
    · rw [FrozenVariableComponents.snoc_deg_castSucc]
      exact (gammaIntegralityLemmas.deg_le_total LLw i).trans (hS.trans hn)
  have h1 := gammaIntegralityLemmas.vW_ge (p := p) m (T := a) (B := Nat.log p (a)) le_rfl hT
  rw [Fin.sum_univ_castSucc] at h1
  simp only [hδ, FrozenVariableComponents.snoc_deg_last, FrozenVariableComponents.snoc_deg_castSucc] at h1
  have h2 : padicValNat p Den = padicValNat p (n - LLw.total).factorial + padicValNat p LLw.total.factorial +
      ∑ i, padicValNat p (LLw.deg i).factorial := by
    rw [hDen, padicValNat.mul (Nat.mul_ne_zero (Nat.factorial_pos _).ne' (Nat.factorial_pos _).ne')
      (Finset.prod_ne_zero_iff.mpr fun i _ => (Nat.factorial_pos _).ne'),
      padicValNat.mul (Nat.factorial_pos _).ne' (Nat.factorial_pos _).ne',
      gammaIntegralityLemmas.v_prod _ _ (fun i _ => (Nat.factorial_pos _).ne')]
  have h3 : padicValNat p (n - LLw.total).factorial + padicValNat p LLw.total.factorial ≤
      padicValNat p n.factorial := by
    have e := Nat.choose_mul_factorial_mul_factorial hS
    rw [← e, padicValNat.mul (Nat.mul_ne_zero (Nat.choose_pos hS).ne' (Nat.factorial_pos _).ne')
      (Nat.factorial_pos _).ne', padicValNat.mul (Nat.choose_pos hS).ne' (Nat.factorial_pos _).ne']
    omega
  have h5 := gammaIntegralityLemmas.norm_K (p := p) ⌈κ⌉₊ (coeff m F) (coeff m F') 0 0 (by simpa using hc m) (by simpa using hc' m)
    Num Den hNum0 hDen0 1 norm_one (by
      have : (padicValNat p Den : ℤ) ≤ (padicValNat p Num : ℤ) + (⌈κ⌉₊ : ℤ) := by
        have : padicValNat p Den ≤ padicValNat p Num + ⌈κ⌉₊ := by
          rw [h2]
          have h1' : ∑ i, padicValNat p (LLw.deg i).factorial + padicValNat p n.factorial ≤
              padicValNat p Num + (K + 2) * (r * Nat.log p (a)) := h1
          omega
        exact_mod_cast this
      omega)
  rw [one_mul] at h5
  exact h5
end Formalism.InvariantFactorPaths.MC
