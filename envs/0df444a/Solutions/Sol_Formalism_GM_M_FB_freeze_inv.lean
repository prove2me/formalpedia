-- Prove2me | solution 1 for Formalism.GM.M.FB.freeze_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:33:42.627606+00:00
-- url     : https://prove2.me/submissions/37cdd424-fc88-4bde-9c39-571eea6abcc9

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Theorems.Thm_Formalism_GM_M_FB_evVal_last
import Theorems.Thm_Formalism_GM_M_FB_evVal_castSucc
import Theorems.Thm_Formalism_GM_M_FB_res_apply
import Theorems.Thm_Formalism_GM_M_FB_ext_last
import Theorems.Thm_Formalism_GM_M_FB_ext_castSucc
import Theorems.Thm_Formalism_GM_M_FB_res_ext
import Theorems.Thm_Formalism_GM_M_FB_glAct_mul
import Theorems.Thm_Formalism_GM_M_FB_glAct_X
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_last
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_last
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_castSucc
import Theorems.Thm_Formalism_GM_M_FB_glAct_aeval_freezeSub
import Theorems.Thm_Formalism_GM_M_FB_glAct_one
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
open Formalism Formalism.GM Formalism.GM.M Formalism.GM.M.FB
open MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.GM.M.FB
theorem _root_.solution (LL : Letters N) (ρ : Fin r) (n : ℕ) (f : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    IsFrozenInv p LL ρ n (freeze p LL ρ n f) := by
  intro c hc
  have hXρ : glAct p (LL.snoc n) (N + 1) c ρ (X (Fin.last N, ρ)) = 0 := by
    rw [glAct_X]
    simp [Ne.symm hc]
  have hpow : ∀ k, glAct p (LL.snoc n) (N + 1) c ρ (X (Fin.last N, ρ) ^ k) = 0 := by
    intro k
    induction k with
    | zero => rw [pow_zero]; exact glAct_one LL n ρ c
    | succ k ih => rw [pow_succ, glAct_mul, ih, hXρ, mul_zero, mul_zero, add_zero]
  unfold freeze
  rw [glAct_mul, hpow, glAct_aeval_freezeSub LL n ρ c hc, mul_zero, mul_zero, add_zero]
end Formalism.GM.M.FB
