-- Prove2me | solution 1 for CookPvsNP.stack_consume
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T13:43:38.020788+00:00
-- url     : https://prove2.me/submissions/0f0dc773-b60c-4aab-801d-ce2f57198cf8

import Definitions.Def_CookPvsNP_StackMacros

set_option autoImplicit false
open CookPvsNP

private theorem consume {K A : Type} [DecidableEq K] (src : K) (targets : K → Bool)
    (w : List A) (s : K → List A) (hs : s src = w) :
    (consumeProg src targets).Exec s (consumeStore src targets s) (3 * w.length + 1) := by
  induction w generalizing s with
  | nil =>
    have hf : consumeStore src targets s = s := by
      funext k
      by_cases hk : k = src <;> simp [consumeStore, hk, hs]
    rw [hf]
    exact .loopFalse (by simp [hs])
  | cons a w ih =>
    let s' := StackProg.applyAct (consumeAct src targets) s
    have hs' : s' src = w := by simp [s', StackProg.applyAct, consumeAct, hs, StackAct.apply]
    have hout : consumeStore src targets s' = consumeStore src targets s := by
      funext k
      by_cases hk : k = src
      · simp [consumeStore, hk]
      · cases ht : targets k <;>
          simp [consumeStore, hk, ht, hs', s', StackProg.applyAct, consumeAct, hs,
            StackAct.apply, List.drop_tail]
    have h := StackProg.Exec.loopTrue (by simp [hs])
      (StackProg.Exec.act (consumeAct src targets) s) (ih s' hs')
    rw [hout] at h
    convert h using 1 <;> simp [consumeProg] <;> omega

theorem solution {K A : Type} [DecidableEq K] (src : K) (targets : K → Bool)
    (s : K → List A) :
    (consumeProg src targets).Exec s (consumeStore src targets s) (3 * (s src).length + 1) := by
  exact consume src targets (s src) s rfl

#print axioms solution
