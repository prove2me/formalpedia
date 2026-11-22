-- Prove2me | solution 1 for Formalism.GM.M.FB.glAct_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:44:52.107846+00:00
-- url     : https://prove2.me/submissions/3f706ce3-3bf6-488a-bf74-77b7cb01279a

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
theorem _root_.solution {M : ℕ} (LL : Letters M) (c d : Fin r) (j : Fin M) (a : Fin r) :
    glAct p LL M c d (X (j, a)) =
      if LL.vec j then (if a = d then X (j, c) else 0) else (if a = c then -X (j, d) else 0) := by
  simp only [glAct, LinearMap.sum_apply]
  rw [Finset.sum_eq_single j]
  · by_cases hv : LL.vec j <;> by_cases ha : a = d <;> by_cases hc : a = c <;>
      simp [hv, ha, hc, MvPolynomial.pderiv_X, Pi.single_apply, j.isLt] <;> split_ifs <;> simp_all
  · intro i _ hij
    split_ifs <;> simp [MvPolynomial.pderiv_X, Pi.single_apply, Ne.symm hij]
  · intro h
    exact absurd (Finset.mem_univ j) h
end Formalism.GM.M.FB
