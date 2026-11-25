-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.MC.partner_condition_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:41:52.255193+00:00
-- url     : https://prove2.me/submissions/31dc3afc-8bac-4bc1-8589-ff89909099e6

import Definitions.Def_Formalism_ThetaLogCoordinates_PartnerMeanCoordinates_TheoremMCB
import Definitions.Def_Formalism_ThetaLogCoordinates_PartnerMeanCoordinates_PartnerMeanProofs_PartnerConditionHolds
import Theorems.Thm_Formalism_CountingSumsFrames_fockN_monomial_ge
import Theorems.Thm_Formalism_CountingSumsFrames_glAct_pol
import Theorems.Thm_Formalism_CountingSumsFrames_isoC_le_ycond
import Theorems.Thm_Formalism_CountingSumsFrames_lcomp_fix
import Theorems.Thm_Formalism_CountingSumsFrames_lcomp_fock
import Theorems.Thm_Formalism_CountingSumsFrames_lcomp_int
import Theorems.Thm_Formalism_CountingSumsFrames_prim_unit_coeff
import Theorems.Thm_Formalism_CountingSumsFrames_proj_fix
import Theorems.Thm_Formalism_CountingSumsFrames_typeProj_pol
import Theorems.Thm_Formalism_CountingSumsFrames_typeProj_ycond
import Theorems.Thm_Formalism_CountingSumsFrames_ycond_glStable
import Theorems.Thm_Formalism_CountingSumsFrames_ycond_le_supp
import Theorems.Thm_Formalism_CountingSumsFrames_ycond_min
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
import Theorems.Thm_Formalism_GM_TM_mem_intPol_of_norm
import Theorems.Thm_P2M_Formalism_CountingSumsFrames_fockN_smul_right__bfa97ee757de
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
theorem _root_.solution : YPartnerC := by
  intro p _ N r _ _ LL q J M ρ e1 hr hHP z hz hprim
  obtain ⟨hP1, hP2⟩ := hHP
  let Tj : Fin (N + 1) → Set (Fin r → ℤ) := fun j =>
    {la | ∀ k, min (J k) N = (j : ℕ) → ((la 0 : ℤ) : WithTop ℤ) ≤ M k}
  have hex : ∀ j : Fin (N + 1), ∃ P, IsTypeProj p LL j univ (Tj j) P ∧ (∀ F G, fock p (P F) G = fock p F (P G)) ∧
      ∀ F ∈ PolZ p r LL, ((p : ℚ_[p]) ^ e1) • P F ∈ IntPol p (Fin N × Fin r) :=
    fun j => hP1 j (Nat.lt_succ_iff.mp j.isLt) univ (Or.inl rfl) (Tj j)
      (fun la la' h => by rw [show la = la' from funext fun c => h c (mem_univ c)])
  choose P hPt hPsa hPint using hex
  have hPP : ∀ j x, P j (P j x) = P j x := fun j x => LinearMap.congr_fun (hPt j).1 x
  have hcomm : ∀ j j' x, P j (P j' x) = P j' (P j x) := by
    intro j j' x
    rcases le_total (j : ℕ) (j' : ℕ) with h | h
    · exact LinearMap.congr_fun (hP2 j j' univ univ (Tj j) (Tj j') (P j) (P j') h subset_rfl (Or.inl rfl)
        (Or.inl rfl) (hPt j) (hPt j')) x
    · exact (LinearMap.congr_fun (hP2 j' j univ univ (Tj j') (Tj j) (P j') (P j) h subset_rfl (Or.inl rfl)
        (Or.inl rfl) (hPt j') (hPt j)) x).symm
  have hPpol : ∀ j, ∀ x ∈ Pol p r LL, P j x ∈ Pol p r LL := fun j => typeProj_pol LL j (Tj j) (P j) (hPt j)

  have hfixY : ∀ j : Fin (N + 1), ∀ x ∈ Y p (r := r) LL J M, P j x = x := by
    intro j
    set S : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
      Pol p r LL ⊓ ⨅ (k : Fin q) (_ : min (J k) N = (j : ℕ)), YCond p (r := r) LL j (M k) with hSdef
    have hmemS : ∀ x, x ∈ S ↔ x ∈ Pol p r LL ∧ ∀ k, min (J k) N = (j : ℕ) → x ∈ YCond p (r := r) LL j (M k) := by
      intro x; simp only [hSdef, Submodule.mem_inf, Submodule.mem_iInf]
    have hfix := proj_fix LL j (Tj j) (P j) (hPt j) S inf_le_left
      (fun c d x hx => by
        rw [hmemS] at hx ⊢
        exact ⟨glAct_pol LL j c d x hx.1, fun k hk => ycond_glStable LL j (M k) c d x (hx.2 k hk)⟩)
      (fun x hx => by
        rw [hmemS] at hx ⊢
        exact ⟨hPpol j x hx.1, fun k hk => typeProj_ycond LL j (Tj j) (P j) (hPt j) (M k) x (hx.2 k hk)⟩)
      (fun h hh hh0 μ hμ => by
        rw [hmemS] at hh
        intro k hk
        have h1 := ycond_le_supp LL j (M k) (hh.2 k hk)
        obtain ⟨m, hm⟩ : ∃ m, m ∈ h.support := by
          by_contra hc; push Not at hc
          exact hh0 (MvPolynomial.support_eq_empty.mp (Finset.eq_empty_of_forall_notMem hc))
        rw [mem_restrictSupport_iff] at h1
        have h2 := h1 (Finset.mem_coe.mpr hm)
        have h3 := (Submodule.mem_inf.mp hμ).1
        rw [WtSpC, mem_restrictSupport_iff] at h3
        have h4 := h3 (Finset.mem_coe.mpr hm) 0 (Finset.mem_univ _)
        simp only [Set.mem_ofPred_eq] at h2
        rw [h4] at h2
        exact h2)
    intro x hx
    apply hfix
    rw [hmemS]
    refine ⟨(Submodule.mem_inf.mp hx).1, fun k hk => ?_⟩
    have := (Submodule.mem_iInf _).mp (Submodule.mem_inf.mp hx).2 k
    rw [ycond_min, hk] at this
    exact this

  have hranY : ∀ j : Fin (N + 1), ∀ u, P j u = u → ∀ k, min (J k) N = (j : ℕ) →
      u ∈ YCond p (r := r) LL (J k) (M k) := by
    intro j u hu k hk
    rw [ycond_min, hk]
    have h1 : u ∈ LinearMap.range (P j) := ⟨u, hu⟩
    rw [(hPt j).2.1] at h1
    exact (iSup₂_le fun la hla => isoC_le_ycond LL j la (M k) (hla k hk)) h1

  obtain ⟨m0, hm0⟩ := prim_unit_coeff LL J M z hz hprim
  have hzY : z ∈ Y p (r := r) LL J M := (Submodule.mem_inf.mp hz).1
  have hzP : z ∈ Pol p r LL := (Submodule.mem_inf.mp (Submodule.mem_inf.mp hz).2).1
  have hm0mem : m0 ∈ z.support := by
    rw [mem_support_iff]; intro h; rw [h, norm_zero] at hm0; exact zero_ne_one hm0
  have hmd : MultiDeg LL m0 := by
    rw [Pol, mem_restrictSupport_iff] at hzP; exact hzP (Finset.mem_coe.mpr hm0mem)
  have hmonZ : (monomial m0 (1 : ℚ_[p])) ∈ PolZ p r LL := by
    classical
    refine Submodule.mem_inf.mpr ⟨?_, mem_intPol_of_norm _ fun m => ?_⟩
    · show monomial m0 (1 : ℚ_[p]) ∈ Pol p r LL
      rw [Pol, mem_restrictSupport_iff]
      intro m hm
      rw [Finset.mem_coe] at hm
      rw [Finset.mem_singleton.mp (support_monomial_subset hm)]
      exact hmd
    · rw [coeff_monomial]; split_ifs <;> simp
  set u := lcomp P (List.finRange (N + 1)) (monomial m0 (1 : ℚ_[p])) with hu
  have hufix : ∀ j, P j u = u := fun j => lcomp_fix P hPP hcomm _ j (List.mem_finRange j) _
  have hint := lcomp_int LL e1 P hPpol hPint (List.finRange (N + 1)) _ hmonZ
  rw [List.length_finRange] at hint
  refine ⟨((p : ℚ_[p]) ^ (e1 * (N + 1))) • u, ?_, ?_⟩
  · refine Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨(Submodule.mem_inf.mp hint).1, ?_⟩, hint⟩
    rw [Submodule.mem_iInf]
    intro k
    refine Submodule.smul_mem _ _ ?_
    exact hranY ⟨min (J k) N, by omega⟩ u (hufix _) k rfl
  ·
    rw [fockN_smul_right', norm_mul, norm_pow, Padic.norm_p]
    have hf : fockN p LL z u = fockN p LL z (monomial m0 1) := by
      unfold fockN
      rw [hu, lcomp_fock P hPsa z (fun j => hfixY j z hzY)]
    rw [hf]
    have hge := fockN_monomial_ge LL z m0 hmd hm0
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    calc (p : ℝ) ^ (-((e1 * (N + 1) : ℕ) : ℤ)) = (p : ℝ)⁻¹ ^ (e1 * (N + 1)) * 1 := by
          rw [zpow_neg, zpow_natCast, inv_pow, mul_one]
      _ ≤ (p : ℝ)⁻¹ ^ (e1 * (N + 1)) * ‖fockN p LL z (monomial m0 1)‖ :=
          mul_le_mul_of_nonneg_left hge (by positivity)
end Formalism.InvariantFactorPaths.MC
