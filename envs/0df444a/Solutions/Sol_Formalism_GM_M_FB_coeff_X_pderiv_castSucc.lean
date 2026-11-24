-- Prove2me | solution 1 for Formalism.GM.M.FB.coeff_X_pderiv_castSucc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:22:25.642916+00:00
-- url     : https://prove2.me/submissions/61bd269b-be8d-4f82-a995-705c89b6b963

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
theorem _root_.solution (ρ : Fin r) (G : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p])
    (m : Fin (N + 1) × Fin r →₀ ℕ)
    (hG : ∀ ν : Fin (N + 1) × Fin r →₀ ℕ, kk ρ ν = kk ρ m → coeff ν G = 0)
    (i : Fin N) (a b : Fin r) :
    coeff m (X (Fin.castSucc i, a) * pderiv (Fin.castSucc i, b) G) = 0 := by
  classical
  rw [MvPolynomial.coeff_X_mul']
  split_ifs with h
  · rw [MvPolynomial.coeff_pderiv, hG _ ?_, zero_mul]
    simp only [kk]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp [Finsupp.single_apply, Fin.castSucc_ne_last]
  · rfl
end Formalism.GM.M.FB
