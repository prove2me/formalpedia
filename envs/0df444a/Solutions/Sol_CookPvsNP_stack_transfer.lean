-- Prove2me | solution 1 for CookPvsNP.stack_transfer
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T13:43:33.682198+00:00
-- url     : https://prove2.me/submissions/d53bebfc-d831-4207-83b8-067d63206803

import Definitions.Def_CookPvsNP_StackMacros

set_option autoImplicit false
open CookPvsNP

private theorem transfer {K A : Type} [DecidableEq K] (src : K) (targets : K → Bool)
    (w : List A) (s : K → List A) (hs : s src = w) :
    (transferProg src targets).Exec s (transferStore src targets s) (3 * w.length + 1) := by
  induction w generalizing s with
  | nil =>
    have hf : transferStore src targets s = s := by
      funext k
      by_cases hk : k = src <;> simp [transferStore, hk, hs]
    rw [hf]
    exact .loopFalse (by simp [hs])
  | cons a w ih =>
    let s' := StackProg.applyAct (transferAct src targets) s
    have hs' : s' src = w := by simp [s', StackProg.applyAct, transferAct, hs, StackAct.apply]
    have hout : transferStore src targets s' = transferStore src targets s := by
      funext k
      by_cases hk : k = src
      · simp [transferStore, hk]
      · cases ht : targets k <;>
          simp [transferStore, hk, ht, hs', s', StackProg.applyAct, transferAct, hs,
            StackAct.apply, List.reverse_cons, List.append_assoc]
    have h := StackProg.Exec.loopTrue (by simp [hs])
      (StackProg.Exec.act (transferAct src targets) s) (ih s' hs')
    rw [hout] at h
    convert h using 1 <;> simp [transferProg] <;> omega

theorem solution {K A : Type} [DecidableEq K] (src : K) (targets : K → Bool)
    (s : K → List A) :
    (transferProg src targets).Exec s (transferStore src targets s) (3 * (s src).length + 1) := by
  exact transfer src targets (s src) s rfl

#print axioms solution
