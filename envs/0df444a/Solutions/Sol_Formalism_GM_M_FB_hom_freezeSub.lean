-- Prove2me | solution 1 for Formalism.GM.M.FB.hom_freezeSub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:26:10.107283+00:00
-- url     : https://prove2.me/submissions/4d3326b0-0c42-4959-acc5-5fbfd5c2809b

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
import Theorems.Thm_Formalism_GM_M_FB_hom_XX
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
theorem _root_.solution (LL : Letters N) (ρ : Fin r) (v : Fin N × Fin r) :
    IsWeightedHomogeneous (wL N r) (freezeSub p LL ρ v) 1 := by
  rcases v with ⟨i, c⟩
  have hw : ∀ c1 c2, IsWeightedHomogeneous (wL N r)
      (X (Fin.castSucc i, c1) * X (Fin.last N, c2) : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) 1 :=
    fun c1 c2 => hom_XX _ _ (by simp [wL, Fin.castSucc_ne_last])
  have hw' : ∀ c1 c2, IsWeightedHomogeneous (wL N r)
      (X (Fin.last N, c2) * X (Fin.castSucc i, c1) : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) 1 :=
    fun c1 c2 => hom_XX _ _ (by simp [wL, Fin.castSucc_ne_last])
  simp only [freezeSub]
  split_ifs
  · rw [← MvPolynomial.mem_weightedHomogeneousSubmodule]
    exact Submodule.sum_mem _ fun c' _ => (MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).2 (hw c' c')
  · exact hw' c ρ
  · exact hw' ρ ρ
  · rw [← MvPolynomial.mem_weightedHomogeneousSubmodule]
    exact Submodule.sub_mem _ ((MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).2 (hw' c ρ))
      ((MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).2 (hw ρ c))
end Formalism.GM.M.FB
