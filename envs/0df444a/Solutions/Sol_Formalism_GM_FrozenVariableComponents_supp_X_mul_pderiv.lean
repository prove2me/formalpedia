-- Prove2me | solution 1 for Formalism.GM.FrozenVariableComponents.supp_X_mul_pderiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:24:34.125812+00:00
-- url     : https://prove2.me/submissions/0a962a55-92e4-474f-a160-d82876b5f735

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_X_mul_pderiv_eq_sum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_castSucc
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_last
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_comb
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_comb

set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.FrozenVariableComponents
open MvPolynomial Finset Formalism.GM.M
variable {K : Type*} [CommRing K] {σ : Type*}
namespace Formalism.GM.FrozenVariableComponents
theorem _root_.solution (a b : σ) (F : MvPolynomial σ K) (m : σ →₀ ℕ)
    (hm : m ∈ (X a * pderiv b F).support) :
    ∃ m0 ∈ F.support, ∀ x, x ≠ a → x ≠ b → m x = m0 x := by
  classical
  by_contra hcon
  push Not at hcon
  apply mem_support_iff.1 hm
  rw [X_mul_pderiv_eq_sum, coeff_sum]
  refine Finset.sum_eq_zero (fun m0 hm0 => ?_)
  rw [coeff_monomial, if_neg]
  intro heq
  obtain ⟨x, hxa, hxb, hx⟩ := hcon m0 hm0
  apply hx
  rw [← heq]
  simp [Ne.symm hxa, Ne.symm hxb]
end Formalism.GM.FrozenVariableComponents
