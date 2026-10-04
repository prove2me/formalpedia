-- Prove2me | solution 1 for CookPvsNP.stack_lookup
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T14:03:56.208997+00:00
-- url     : https://prove2.me/submissions/2503a7e9-2462-410b-8cef-b320623e47a5

import Definitions.Def_CookPvsNP_StackLookup
import Theorems.Thm_CookPvsNP_stack_copy
import Theorems.Thm_CookPvsNP_stack_consume
import Theorems.Thm_CookPvsNP_stack_basic_macros

set_option autoImplicit false
open CookPvsNP

private theorem drop_head {A : Type} (w : List A) (n : ℕ) (a : A) :
    (w.drop n).headD a = w.getD n a := by
  induction n generalizing w with
  | zero => cases w <;> rfl
  | succ n ih => cases w <;> simp [List.getD, ih]

theorem solution {K A : Type} [DecidableEq K] (r : Fin 6 ↪ K) (fallback : A)
    (s : K → List A) (h2 : s (r 2) = []) (h3 : s (r 3) = [])
    (h4 : s (r 4) = []) (h5 : s (r 5) = []) :
    ∃ n ≤ 9 * (s (r 0)).length + 9 * (s (r 1)).length + 13,
      (lookupProg r fallback).Exec s
        (Function.update s (r 2) [(s (r 0)).getD (s (r 1)).length fallback]) n := by
  have neq (i j : Fin 6) (h : i ≠ j) : r i ≠ r j := r.injective.ne h
  have eqs (i j : Fin 6) : (r i = r j) ↔ i = j := r.injective.eq_iff
  let s1 := Function.update s (r 3) (s (r 0))
  let s2 := Function.update s1 (r 4) (s (r 1))
  let s3 := Function.update (Function.update s (r 3) ((s (r 0)).drop (s (r 1)).length)) (r 4) []
  let value := (s (r 0)).getD (s (r 1)).length fallback
  let s4 := Function.update s3 (r 2) [value]
  have hcopy1 := stack_copy (r 0) (r 3) (r 5)
    (neq _ _ (by decide)) (neq _ _ (by decide)) (neq _ _ (by decide)) s h5
  simp only [h3, List.append_nil] at hcopy1
  have hcopy2 := stack_copy (r 1) (r 4) (r 5)
    (neq _ _ (by decide)) (neq _ _ (by decide)) (neq _ _ (by decide)) s1
    (by simp [s1, Function.update, eqs, h5])
  simp [s1, eqs, h4] at hcopy2
  have hconsume := stack_consume (r 4) (fun k => decide (k = r 3)) s2
  have hs3 : consumeStore (r 4) (fun k => decide (k = r 3)) s2 = s3 := by
    funext k
    by_cases hk : k = r 4
    · subst k; simp [consumeStore, s3]
    by_cases hk' : k = r 3
    · subst k; simp [consumeStore, s2, s1, s3, Function.update, eqs]
    · simp [consumeStore, s2, s1, s3, Function.update, hk, hk']
  rw [hs3] at hconsume
  have hpeek : (StackProg.act (peekPushAct (r 3) (r 2) fallback)).Exec s3 s4 1 := by
    have he : StackProg.applyAct (peekPushAct (r 3) (r 2) fallback) s3 = s4 := by
      funext k
      by_cases hk : k = r 2
      · subst k
        simp [s4, s3, StackProg.applyAct, peekPushAct, StackAct.apply,
          Function.update, eqs, h2, value, List.headD, drop_head]
      · simp [s4, StackProg.applyAct, peekPushAct, StackAct.apply, Function.update, hk]
    simpa only [he] using StackProg.Exec.act (peekPushAct (r 3) (r 2) fallback) s3
  have hclear := (stack_basic_macros (r 3) s4).2.2
  have hf : Function.update s4 (r 3) [] = Function.update s (r 2) [value] := by
    funext k
    by_cases hk : k = r 3
    · subst k; simp [Function.update, eqs, h3]
    by_cases hk' : k = r 4
    · subst k; simp [s4, s3, Function.update, eqs, h4]
    · simp [s4, s3, Function.update, hk, hk']
  rw [hf] at hclear
  have hprog := StackProg.Exec.seq hcopy1 (StackProg.Exec.seq hcopy2
    (StackProg.Exec.seq hconsume (StackProg.Exec.seq hpeek hclear)))
  refine ⟨_, ?_, hprog⟩
  simp [s4, s3, s2, s1, Function.update, eqs, List.length_drop]
  omega

#print axioms solution
