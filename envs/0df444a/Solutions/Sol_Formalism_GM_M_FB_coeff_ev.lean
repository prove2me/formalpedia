-- Prove2me | solution 1 for Formalism.GM.M.FB.coeff_ev
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:26:57.756925+00:00
-- url     : https://prove2.me/submissions/c463959d-189e-4972-bde0-d86edd518161

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Theorems.Thm_Formalism_GM_M_FB_evVal_last
import Theorems.Thm_Formalism_GM_M_FB_evVal_castSucc
import Theorems.Thm_Formalism_GM_M_FB_res_apply
import Theorems.Thm_Formalism_GM_M_FB_ext_last
import Theorems.Thm_Formalism_GM_M_FB_ext_castSucc
import Theorems.Thm_Formalism_GM_M_FB_res_ext
import Theorems.Thm_Formalism_GM_M_FB_ev_monomial
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

set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.M Formalism.GM.M.FB
open MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.GM.M.FB
theorem _root_.solution (ρ : Fin r) (n : ℕ) (F : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p])
    (hF : ∀ m ∈ F.support, ∑ c, m (Fin.last N, c) = n) (m' : Fin N × Fin r →₀ ℕ) :
    coeff m' (ev p ρ F) = coeff (ext n ρ m') F := by
  classical
  conv_lhs => rw [F.as_sum]
  rw [map_sum, MvPolynomial.coeff_sum]
  simp only [ev_monomial]
  rw [Finset.sum_eq_single (ext n ρ m')]
  · rw [if_pos (fun c hc => by rw [ext_last, if_neg hc]), res_ext, MvPolynomial.coeff_monomial, if_pos rfl]
  · intro m hm hne
    split_ifs with hcond
    · rw [MvPolynomial.coeff_monomial, if_neg]
      intro hres
      apply hne
      have heq : m = ext n ρ (res m) := by
        ext ⟨i, c⟩
        refine Fin.lastCases ?_ (fun j => ?_) i
        · by_cases hc : c = ρ
          · subst hc
            rw [ext_last, if_pos rfl, ← hF m hm, Finset.sum_eq_single c]
            · intro b _ hb
              exact hcond b hb
            · intro h
              exact absurd (Finset.mem_univ c) h
          · rw [ext_last, if_neg hc, hcond c hc]
        · rw [ext_castSucc, res_apply]
      rw [heq, hres]
    · exact MvPolynomial.coeff_zero _
  · intro hnot
    have h0 : coeff (ext n ρ m') F = 0 := by simpa using hnot
    rw [h0]
    split_ifs <;> simp
end Formalism.GM.M.FB
