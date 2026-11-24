-- Prove2me | solution 1 for Formalism.GM.M.FB.vanish
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:25:22.018576+00:00
-- url     : https://prove2.me/submissions/08586afe-f74b-4fee-bb63-57dcfda543db

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Theorems.Thm_Formalism_GM_M_FB_evVal_last
import Theorems.Thm_Formalism_GM_M_FB_evVal_castSucc
import Theorems.Thm_Formalism_GM_M_FB_res_apply
import Theorems.Thm_Formalism_GM_M_FB_ext_last
import Theorems.Thm_Formalism_GM_M_FB_ext_castSucc
import Theorems.Thm_Formalism_GM_M_FB_res_ext
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_last
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_last
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_castSucc
import Theorems.Thm_Formalism_GM_M_FB_coeff_X_pderiv_castSucc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.M.FB.evVal_last
attribute [local simp] Formalism.GM.M.FB.evVal_castSucc
attribute [local simp] Formalism.GM.M.FB.res_apply
attribute [local simp] Formalism.GM.M.FB.ext_last
attribute [local simp] Formalism.GM.M.FB.ext_castSucc
attribute [local simp] Formalism.GM.M.FB.res_ext
attribute [local simp] Formalism.GM.M.FB.snoc_vec_last
attribute [local simp] Formalism.GM.M.FB.snoc_vec_castSucc
attribute [local simp] Formalism.GM.M.FB.snoc_deg_last
attribute [local simp] Formalism.GM.M.FB.snoc_deg_castSucc

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSimpArgs false
open Formalism Formalism.GM Formalism.GM.M Formalism.GM.M.FB
open MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.GM.M.FB
theorem _root_.solution (LL : Letters N) (n : ℕ) (ρ : Fin r) (G : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p])
    (hinv : IsFrozenInv p LL ρ n G) (h0 : ∀ m, kk ρ m = 0 → coeff m G = 0) : G = 0 := by
  classical
  by_contra hne
  have hex : ∃ k, ∃ m, kk ρ m = k ∧ coeff m G ≠ 0 := by
    obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.1 hne
    exact ⟨_, m, rfl, hm⟩
  obtain ⟨m, hmk, hm⟩ := Nat.find_spec hex
  have hmin : ∀ ν, kk ρ ν < Nat.find hex → coeff ν G = 0 := fun ν hν => by
    by_contra h
    exact Nat.find_min hex hν ⟨ν, rfl, h⟩
  obtain ⟨c, hcρ, hc⟩ : ∃ c, c ≠ ρ ∧ m (Fin.last N, c) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hm
    apply h0
    simp only [kk]
    exact Finset.sum_eq_zero fun c' hc' => hcon c' (Finset.ne_of_mem_erase hc')
  set m' := m - Finsupp.single (Fin.last N, c) 1 + Finsupp.single (Fin.last N, ρ) 1 with hm'
  have hval : ∀ c', c' ≠ ρ → m' (Fin.last N, c') = m (Fin.last N, c') - (if c = c' then 1 else 0) := by
    intro c' hc'
    simp [hm', Finsupp.single_apply, Ne.symm hc']
  have hlt : kk ρ m' < kk ρ m := by
    simp only [kk]
    refine Finset.sum_lt_sum (fun c' hc' => ?_) ⟨c, Finset.mem_erase.2 ⟨hcρ, Finset.mem_univ _⟩, ?_⟩
    · rw [hval c' (Finset.ne_of_mem_erase hc')]
      exact Nat.sub_le _ _
    · rw [hval c hcρ, if_pos rfl]
      omega
  have hG' : ∀ ν, kk ρ ν = kk ρ m' → coeff ν G = 0 := fun ν hν => hmin ν (hν ▸ hmk ▸ hlt)
  have hc0 := congrArg (coeff m') (hinv c hcρ)
  simp only [glAct, LinearMap.sum_apply, MvPolynomial.coeff_sum, coeff_zero] at hc0
  rw [Fin.sum_univ_castSucc, Finset.sum_eq_zero (fun i _ => ?_), zero_add] at hc0
  · have hl : ((Fin.last N : Fin (N + 1)) : ℕ) < N + 1 := (Fin.last N).isLt
    rw [if_pos hl] at hc0
    simp only [snoc_vec_last, Bool.false_eq_true, ↓reduceIte, LinearMap.neg_apply, LinearMap.comp_apply,
      LinearMap.mulLeft_apply, coeff_neg, neg_eq_zero] at hc0
    rw [MvPolynomial.coeff_X_mul', if_pos (by simp [hm'])] at hc0
    erw [MvPolynomial.coeff_pderiv] at hc0
    have e1 : m' - Finsupp.single (Fin.last N, ρ) 1 + Finsupp.single (Fin.last N, c) 1 = m := by
      rw [hm', add_tsub_cancel_right,
        tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hc))]
    have e2 : ((m' - Finsupp.single (Fin.last N, ρ) 1 : Fin (N + 1) × Fin r →₀ ℕ) (Fin.last N, c)) + 1 =
        m (Fin.last N, c) := by
      rw [hm', add_tsub_cancel_right, Finsupp.tsub_apply, Finsupp.single_eq_same]
      omega
    rw [e1] at hc0
    have e3 : ((((m' - Finsupp.single (Fin.last N, ρ) 1 : Fin (N + 1) × Fin r →₀ ℕ) (Fin.last N, c) : ℕ) :
        ℚ_[p]) + 1) = ((m (Fin.last N, c) : ℕ) : ℚ_[p]) := by exact_mod_cast e2
    rw [e3] at hc0
    rcases mul_eq_zero.1 hc0 with h | h
    · exact hm h
    · exact hc (by exact_mod_cast h)
  · have hci : ((Fin.castSucc i : Fin (N + 1)) : ℕ) < N + 1 := (Fin.castSucc i).isLt
    rw [if_pos hci]
    split_ifs
    · simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply]
      exact coeff_X_pderiv_castSucc ρ G m' hG' i c ρ
    · simp only [LinearMap.neg_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply, coeff_neg, neg_eq_zero]
      exact coeff_X_pderiv_castSucc ρ G m' hG' i ρ c
end Formalism.GM.M.FB
