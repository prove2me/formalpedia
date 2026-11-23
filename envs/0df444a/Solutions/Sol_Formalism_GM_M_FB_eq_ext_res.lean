-- Prove2me | solution 1 for Formalism.GM.M.FB.eq_ext_res
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:47:23.657213+00:00
-- url     : https://prove2.me/submissions/cfa4c97f-7946-4375-b3dc-c219031d018e

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
set_option linter.unusedSimpArgs false
open Formalism Formalism.GM Formalism.GM.M Formalism.GM.M.FB
open MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.GM.M.FB
theorem _root_.solution (n : ℕ) (ρ : Fin r) (m : Fin (N + 1) × Fin r →₀ ℕ)
    (hZ : ∀ c, c ≠ ρ → m (Fin.last N, c) = 0) (hrow : ∑ c, m (Fin.last N, c) = n) :
    m = ext n ρ (res m) := by
  ext ⟨i, c⟩
  refine Fin.lastCases ?_ (fun j => ?_) i
  · by_cases hc : c = ρ
    · subst hc
      rw [ext_last, if_pos rfl, ← hrow, Finset.sum_eq_single c]
      · intro b _ hb
        exact hZ b hb
      · intro h
        exact absurd (Finset.mem_univ c) h
    · rw [ext_last, if_neg hc, hZ c hc]
  · rw [ext_castSucc, res_apply]
end Formalism.GM.M.FB
