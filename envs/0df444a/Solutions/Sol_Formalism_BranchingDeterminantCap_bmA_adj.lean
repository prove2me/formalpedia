-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmA_adj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:22:23.403205+00:00
-- url     : https://prove2.me/submissions/956f6856-e01d-49d6-9885-791420ec5953

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmA_prod_update_zero
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmA_prod_update_succ
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_prod
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
variable {A : Type*} [Ring A]
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution : ∀ {n : ℕ} (g : Fin n → A) (p p' : Fin n), p'.val = p.val + 1 →
    ∃ L Rr : A, ∀ a b : A,
      (List.ofFn (Function.update (Function.update g p a) p' b)).prod = L * (a * b) * Rr
  | 0, _, p, _, _ => p.elim0
  | n + 1, g, p, p', h => by
    obtain ⟨q', rfl⟩ : ∃ q' : Fin n, p' = q'.succ := by
      refine ⟨⟨p'.val - 1, by omega⟩, ?_⟩
      ext; simp; omega
    induction p using Fin.cases with
    | zero =>
      have hq : q'.val = 0 := by simpa using h
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := q'.isLt; omega⟩
      have hq0 : q' = 0 := by ext; simpa using hq
      subst hq0
      refine ⟨1, (List.ofFn fun i : Fin m => g i.succ.succ).prod, fun a b => ?_⟩
      rw [bmA_prod_update_succ, Function.update_self, bmA_prod_update_zero]
      have : (fun i : Fin m => Function.update g 0 a i.succ.succ) = fun i : Fin m => g i.succ.succ := by
        funext i
        rw [Function.update_of_ne (Fin.succ_ne_zero _)]
      rw [this]
      noncomm_ring
    | succ q =>
      have hq : q'.val = q.val + 1 := by simpa using h
      obtain ⟨L, Rr, hL⟩ := solution (fun i : Fin n => g i.succ) q q' hq
      refine ⟨g 0 * L, Rr, fun a b => ?_⟩
      rw [bmA_prod_update_succ, Function.update_of_ne (Fin.succ_ne_zero q).symm]
      have : (fun i : Fin n => Function.update g q.succ a i.succ) =
          Function.update (fun i : Fin n => g i.succ) q a := by
        funext i
        by_cases hi : i = q
        · subst hi; simp
        · rw [Function.update_of_ne hi, Function.update_of_ne (fun h' => hi (Fin.succ_injective _ h'))]
      rw [this, hL]
      noncomm_ring
end Formalism.BranchingDeterminantCap
