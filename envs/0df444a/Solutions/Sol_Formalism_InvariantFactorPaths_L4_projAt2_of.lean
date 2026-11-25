-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.projAt2_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:38:15.691496+00:00
-- url     : https://prove2.me/submissions/79a90a13-5ab0-46bf-9ef7-2c94f194ff98

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementH
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_GramBoundUnconditionalOfSat
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_Vanish
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_GramBoundPosOfProjSat
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
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_coeff_pow_mul_ne
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_fock_eq_zero_of
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_fock_pow_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_grSpan_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_monomial_single_add
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_multiDeg_pow
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_pow_mul_int_iff
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_strip_monomial_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_strip_monomial_ne
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_xH_le_free
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
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames Formalism.InvariantFactorPaths.PW MvPolynomial Finset
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (hX : HighestVectorProjectionPos) (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LLw : Letters (K + 1)) {q : ℕ}
    (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r) (w : Fin r → ℤ) (e e1 : ℕ) (hK : 1 ≤ K) (hr : 2 ≤ r)
    (hρ : (ρ : ℕ) = r - 1) (hv : LLw.vec (Fin.last K) = true) (he : e ≤ LLw.deg (Fin.last K))
    (hP : HypP p (setLast LLw (LLw.deg (Fin.last K) - e)) ρ e1)
    (hE : HypE p (setLast LLw (LLw.deg (Fin.last K) - e)) ρ e1)
    (hO : ResOntoK p (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ) :
    ProjAt p LLw J M ρ w e ((K + 1) * e1) := by
  classical
  obtain ⟨Pr', hPr'⟩ := hX p K r (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ (shiftWt w ρ e) e1
    hK hr hρ hv hP hE
  have hSp := grSpan_eq LLw J M ρ w e e1 hr hρ hv he hP hE hO
  refine ⟨(LinearMap.mulLeft ℚ_[p] (X (Fin.last K, ρ) ^ e : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p])) ∘ₗ Pr' ∘ₗ
    strip p (Fin.last K, ρ) e, ?_⟩
  intro m hm
  simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply]
  by_cases hme : m (Fin.last K, ρ) = e
  · obtain ⟨m', rfl⟩ : ∃ m', m = Finsupp.single (Fin.last K, ρ) e + m' :=
      ⟨m - Finsupp.single (Fin.last K, ρ) e, (add_tsub_cancel_of_le (by
        rw [Finsupp.single_le_iff]; exact hme.ge)).symm⟩
    have hm0 : m' (Fin.last K, ρ) = 0 := by simpa using hme
    have hmD := (multiDeg_pow LLw ρ e he m').mp hm
    obtain ⟨h1, h2, h3⟩ := hPr' m' hmD hm0
    rw [strip_monomial_eq _ _ _ hm0]
    refine ⟨(hSp _).mpr ⟨_, h1, rfl⟩, ?_, ?_⟩
    · rw [← mul_smul_comm, pow_mul_int_iff]; exact h2
    · intro g hg
      obtain ⟨y, hy, rfl⟩ := (hSp g).mp hg
      rw [monomial_single_add, fock_pow_mul _ _ _ _ (xH_le_free _ J _ ρ _ y hy),
        fock_pow_mul _ _ _ _ (xH_le_free _ J _ ρ _ y hy), h3 y hy]
  · rw [strip_monomial_ne _ _ _ hme, map_zero, mul_zero]
    refine ⟨Submodule.zero_mem _, by rw [smul_zero]; exact Submodule.zero_mem _, ?_⟩
    intro g hg
    obtain ⟨y, hy, rfl⟩ := (hSp g).mp hg
    rw [fock_eq_zero_of _ 0 (fun _ => Or.inr (coeff_zero _)), fock_eq_zero_of]
    intro n
    by_cases hn : n = m
    · left
      rw [hn]
      exact coeff_pow_mul_ne _ _ y (xH_le_free _ J _ ρ _ y hy) m hme
    · right
      rw [coeff_monomial, if_neg (Ne.symm hn)]
end Formalism.InvariantFactorPaths.L4
