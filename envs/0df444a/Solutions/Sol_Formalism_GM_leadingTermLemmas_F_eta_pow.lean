-- Prove2me | solution 1 for Formalism.GM.leadingTermLemmas.F_eta_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:26:12.187653+00:00
-- url     : https://prove2.me/submissions/01092110-5c76-4c69-bfd4-9bff94b4eafd

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamLead
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_comb
import Theorems.Thm_Formalism_GM_M_FB_evVal_castSucc
import Theorems.Thm_Formalism_GM_M_FB_evVal_last
import Theorems.Thm_Formalism_GM_M_FB_ext_castSucc
import Theorems.Thm_Formalism_GM_M_FB_ext_last
import Theorems.Thm_Formalism_GM_M_FB_res_apply
import Theorems.Thm_Formalism_GM_M_FB_res_ext
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_last
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_last
import Theorems.Thm_P2M_Formalism_GM_tieF_apply__aa4421b36bb1
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_castSucc
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_last
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_comb
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_comb
attribute [local simp] Formalism.GM.M.FB.evVal_castSucc
attribute [local simp] Formalism.GM.M.FB.evVal_last
attribute [local simp] Formalism.GM.M.FB.ext_castSucc
attribute [local simp] Formalism.GM.M.FB.ext_last
attribute [local simp] Formalism.GM.M.FB.res_apply
attribute [local simp] Formalism.GM.M.FB.res_ext
attribute [local simp] Formalism.GM.M.FB.snoc_deg_castSucc
attribute [local simp] Formalism.GM.M.FB.snoc_deg_last
attribute [local simp] Formalism.GM.M.FB.snoc_vec_castSucc
attribute [local simp] Formalism.GM.M.FB.snoc_vec_last



set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.leadingTermLemmas
open MvPolynomial Finset Formalism.GM
variable {K : Type} [Field K] {N r : ℕ} (LL : M.Letters (N + 1)) (ρ : Fin r)
namespace Formalism.GM.leadingTermLemmas
theorem _root_.solution (k : ℕ) (g : MvPolynomial (Fin (N + 1 + 1) × Fin r) K)
    (hg : pderiv (wW (N := N) ρ) g = 0) :
    tieF (wW (N := N)) eη (X (Fin.last (N + 1), ρ) ^ k * g) = X (Fin.last (N + 1), ρ) ^ k * tieF (wW (N := N)) eη g := by
  rw [tieF_apply', tieF_apply', Finset.mul_sum]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  have h1 : pderiv (wW (N := N) c) (X (Fin.last (N + 1), ρ) : MvPolynomial (Fin (N + 1 + 1) × Fin r) K) = 0 := by
    apply pderiv_X_of_ne; intro h; simp only [wW, Prod.mk.injEq] at h; exact Fin.castSucc_ne_last _ h.1.symm
  by_cases hc : c = ρ
  · subst hc
    simp only [pderiv_mul, pderiv_pow, h1, hg, pderiv_X_self, mul_zero, zero_mul, add_zero, mul_one]
    simp [pderiv_mul, hg, h1]
  · rw [pderiv_mul, pderiv_pow, pderiv_X_of_ne (by simp [eη, Ne.symm hc] : (Fin.last (N + 1), ρ) ≠ eη (N := N) c)]
    simp [pderiv_mul, pderiv_pow, h1]
end Formalism.GM.leadingTermLemmas
