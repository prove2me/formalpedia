-- Prove2me | solution 1 for Formalism.GM.GammaExpansion.pow_Dp_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:45:05.5488+00:00
-- url     : https://prove2.me/submissions/b039f205-298b-4596-8283-4eb8d88c7179

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamDeg
import Theorems.Thm_Formalism_GM_GammaExpansion_Dp_apply
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
open Formalism Formalism.GM Formalism.GM.GammaExpansion
open MvPolynomial Finset
variable {R σ : Type} [CommSemiring R]
namespace Formalism.GM.GammaExpansion
theorem _root_.solution (v : σ) (s : σ →₀ ℕ) (c : R) (k : ℕ) :
    (Dp v ^ k) (monomial s c) = monomial (s - Finsupp.single v k) (c * ((s v).descFactorial k : R)) := by
  classical
  induction k generalizing s c with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    show (Dp v ^ k) (Dp v (monomial s c)) = _
    rw [Dp_apply, pderiv_monomial, ih]
    have h1 : s - Finsupp.single v 1 - Finsupp.single v k = s - Finsupp.single v (k + 1) := by
      ext x; simp only [Finsupp.tsub_apply, Finsupp.single_apply]; split_ifs <;> omega
    have h2 : c * ((s v : ℕ) : R) * ((((s - Finsupp.single v 1 : σ →₀ ℕ) v).descFactorial k : ℕ) : R) =
        c * (((s v).descFactorial (k + 1) : ℕ) : R) := by
      rw [Finsupp.tsub_apply, Finsupp.single_eq_same]
      rcases Nat.eq_zero_or_pos (s v) with h | h
      · simp [h]
      · obtain ⟨m, hm⟩ : ∃ m, s v = m + 1 := ⟨s v - 1, by omega⟩
        rw [hm, Nat.add_sub_cancel, Nat.succ_descFactorial_succ]; push_cast; ring
    rw [h1, h2]
end Formalism.GM.GammaExpansion
