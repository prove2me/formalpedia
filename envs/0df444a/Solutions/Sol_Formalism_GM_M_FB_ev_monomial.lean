-- Prove2me | solution 1 for Formalism.GM.M.FB.ev_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:23:42.053791+00:00
-- url     : https://prove2.me/submissions/86b2dbcd-aa65-46c7-ba67-0b8b8cbb4061

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Theorems.Thm_Formalism_GM_M_FB_evVal_last
import Theorems.Thm_Formalism_GM_M_FB_evVal_castSucc
import Theorems.Thm_Formalism_GM_M_FB_res_apply
import Theorems.Thm_Formalism_GM_M_FB_ext_last
import Theorems.Thm_Formalism_GM_M_FB_ext_castSucc
import Theorems.Thm_Formalism_GM_M_FB_res_ext
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
theorem _root_.solution (ρ : Fin r) (m : Fin (N + 1) × Fin r →₀ ℕ) (a : ℚ_[p]) :
    ev p ρ (monomial m a) =
      if (∀ c, c ≠ ρ → m (Fin.last N, c) = 0) then monomial (res m) a else 0 := by
  classical
  rw [ev, MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type,
    Fin.prod_univ_castSucc]
  simp only [evVal_castSucc, evVal_last]
  split_ifs with h
  · have hlast : ∏ c : Fin r, (if c = ρ then (1 : MvPolynomial (Fin N × Fin r) ℚ_[p]) else 0) ^
        m (Fin.last N, c) = 1 := by
      refine Finset.prod_eq_one (fun c _ => ?_)
      by_cases hc : c = ρ
      · simp [hc]
      · simp [hc, h c hc]
    rw [hlast, mul_one, MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
      Fintype.prod_prod_type]
    simp only [res_apply, MvPolynomial.algebraMap_eq]
  · push_neg at h
    obtain ⟨c, hc, hc0⟩ := h
    rw [Finset.prod_eq_zero (Finset.mem_univ c) (by simp [hc, hc0]), mul_zero, mul_zero]
end Formalism.GM.M.FB
