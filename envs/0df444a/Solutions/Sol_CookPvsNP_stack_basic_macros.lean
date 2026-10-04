-- Prove2me | solution 1 for CookPvsNP.stack_basic_macros
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T13:43:36.650992+00:00
-- url     : https://prove2.me/submissions/5bd9c107-ba8e-4a76-ba3c-3e402e22a41b

import Definitions.Def_CookPvsNP_StackMacros
import Theorems.Thm_CookPvsNP_stack_transfer

set_option autoImplicit false
open CookPvsNP

theorem solution {K A : Type} [DecidableEq K] (k : K) (s : K → List A) :
    (∀ a : A, (pushProg k a).Exec s (Function.update s k (a :: s k)) 1) ∧
    (popProg k).Exec s (Function.update s k (s k).tail) 1 ∧
    (clearProg k).Exec s (Function.update s k []) (3 * (s k).length + 1) := by
  constructor
  · intro a
    have he : StackProg.applyAct (fun _ j => if j = k then .push a else .keep) s =
        Function.update s k (a :: s k) := by
      funext j; by_cases h : j = k <;> simp [StackProg.applyAct, h, StackAct.apply]
    simpa [pushProg, he] using StackProg.Exec.act (fun _ j => if j = k then .push a else .keep) s
  constructor
  · have he : StackProg.applyAct (fun _ j => if j = k then .pop else .keep) s =
        Function.update s k (s k).tail := by
      funext j; by_cases h : j = k <;> simp [StackProg.applyAct, h, StackAct.apply]
    simpa [popProg, he] using StackProg.Exec.act (fun _ j => if j = k then .pop else .keep) s
  · have he : transferStore k (fun _ => false) s = Function.update s k [] := by
      funext j; by_cases h : j = k <;> simp [transferStore, h]
    simpa [clearProg, he] using stack_transfer k (fun _ => false) s

#print axioms solution
