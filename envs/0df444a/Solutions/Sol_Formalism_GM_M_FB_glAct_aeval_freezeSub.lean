-- Prove2me | solution 1 for Formalism.GM.M.FB.glAct_aeval_freezeSub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:26:58.929526+00:00
-- url     : https://prove2.me/submissions/f9f472ef-8305-4f17-bcab-4f826ad1de59

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Theorems.Thm_Formalism_GM_M_FB_evVal_last
import Theorems.Thm_Formalism_GM_M_FB_evVal_castSucc
import Theorems.Thm_Formalism_GM_M_FB_res_apply
import Theorems.Thm_Formalism_GM_M_FB_ext_last
import Theorems.Thm_Formalism_GM_M_FB_ext_castSucc
import Theorems.Thm_Formalism_GM_M_FB_res_ext
import Theorems.Thm_Formalism_GM_M_FB_glAct_mul
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_last
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_last
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_castSucc
import Theorems.Thm_Formalism_GM_M_FB_glAct_freezeSub
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
open Formalism Formalism.GM Formalism.GM.M Formalism.GM.M.FB
open MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.GM.M.FB
theorem _root_.solution (LL : Letters N) (n : ℕ) (ρ c : Fin r) (hc : c ≠ ρ)
    (f : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    glAct p (LL.snoc n) (N + 1) c ρ (aeval (freezeSub p LL ρ) f) = 0 := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    have h1 : glAct p (LL.snoc n) (N + 1) c ρ (1 : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) = 0 := by
      simp only [glAct, LinearMap.sum_apply]
      refine Finset.sum_eq_zero fun i _ => ?_
      split_ifs <;> simp
    rw [MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, MvPolynomial.C_eq_smul_one, map_smul, h1, smul_zero]
  | add f g hf hg => rw [map_add, map_add, hf, hg, add_zero]
  | mul_X f v hf =>
    rw [map_mul, MvPolynomial.aeval_X, glAct_mul, hf, glAct_freezeSub LL n ρ c hc v, mul_zero, mul_zero,
      add_zero]
end Formalism.GM.M.FB
