-- Prove2me | solution 1 for Formalism.GM.M.FB.weight_wL
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:00:23.906313+00:00
-- url     : https://prove2.me/submissions/a24848ff-7d49-4a23-99b6-d87e86f8f985

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
open Formalism Formalism.GM Formalism.GM.M Formalism.GM.M.FB
open MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.GM.M.FB
theorem _root_.solution (m : Fin (N + 1) × Fin r →₀ ℕ) :
    Finsupp.weight (wL N r) m = ∑ c, m (Fin.last N, c) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  rw [Fintype.sum_prod_type, Fin.sum_univ_castSucc]
  simp [wL, Fin.castSucc_ne_last]
end Formalism.GM.M.FB
