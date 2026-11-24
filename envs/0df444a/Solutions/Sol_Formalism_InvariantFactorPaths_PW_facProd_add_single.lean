-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.facProd_add_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:50:16.026958+00:00
-- url     : https://prove2.me/submissions/5e8f7826-41af-4175-bb62-a4674e229f8e

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_FischerAdjointnessHolds
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
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {σ : Type}
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution (m : σ →₀ ℕ) (i : σ) :
    ((m + Finsupp.single i 1).prod fun _ k => (k.factorial : ℚ_[p])) =
      ((m i : ℚ_[p]) + 1) * (m.prod fun _ k => (k.factorial : ℚ_[p])) := by
  classical
  have hs1 : (m + Finsupp.single i 1).support ⊆ insert i m.support := by
    intro x hx
    by_cases h : x = i
    · rw [h]
      exact Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      rw [Finsupp.mem_support_iff] at hx ⊢
      have h1 : (Finsupp.single i 1 : σ →₀ ℕ) x = 0 := by simp [Finsupp.single_apply, Ne.symm h]
      simpa [h1] using hx
  have hs2 : m.support ⊆ insert i m.support := Finset.subset_insert _ _
  rw [Finsupp.prod_of_support_subset _ hs1 _ (by simp),
    Finsupp.prod_of_support_subset _ hs2 _ (by simp),
    ← Finset.mul_prod_erase _ _ (Finset.mem_insert_self i m.support),
    ← Finset.mul_prod_erase _ _ (Finset.mem_insert_self i m.support), ← mul_assoc]
  congr 1
  · simp [Nat.factorial_succ]
  · refine Finset.prod_congr rfl fun x hx => ?_
    have hx' : x ≠ i := Finset.ne_of_mem_erase hx
    have h1 : (Finsupp.single i 1 : σ →₀ ℕ) x = 0 := by simp [Finsupp.single_apply, Ne.symm hx']
    rw [Finsupp.add_apply, h1, add_zero]
end Formalism.InvariantFactorPaths.PW
