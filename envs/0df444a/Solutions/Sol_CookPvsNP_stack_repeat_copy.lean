-- Prove2me | solution 1 for CookPvsNP.stack_repeat_copy
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T14:03:57.203005+00:00
-- url     : https://prove2.me/submissions/96871244-0836-45c0-97fb-91d45f5abcbb

import Definitions.Def_CookPvsNP_StackRepeat
import Theorems.Thm_CookPvsNP_stack_copy
import Theorems.Thm_CookPvsNP_stack_basic_macros

set_option autoImplicit false
open CookPvsNP

private theorem repeat_copy {K A : Type} [DecidableEq K] (r : Fin 4 ↪ K)
    (w : List A) (s : K → List A) (hs : s (r 2) = w) (he : s (r 3) = []) :
    (repeatCopyProg r).Exec s
      (Function.update (Function.update s (r 2) []) (r 1)
        ((List.replicate w.length (s (r 0))).flatten ++ s (r 1)))
      ((6 * (s (r 0)).length + 7) * w.length + 1) := by
  have neq (i j : Fin 4) (h : i ≠ j) : r i ≠ r j := r.injective.ne h
  have eqs (i j : Fin 4) : (r i = r j) ↔ i = j := r.injective.eq_iff
  induction w generalizing s with
  | nil =>
    have hf : Function.update (Function.update s (r 2) []) (r 1) (s (r 1)) = s := by
      funext k
      by_cases hk : k = r 2
      · subst k; simp [Function.update, eqs, hs]
      by_cases hk' : k = r 1
      · subst k; simp [Function.update]
      · simp [Function.update, hk, hk']
    simp only [List.length_nil, Nat.mul_zero, Nat.zero_add, List.replicate_zero,
      List.flatten_nil, List.nil_append, hf]
    exact .loopFalse (by simp [hs])
  | cons a w ih =>
    let s1 := Function.update s (r 2) w
    let s2 := Function.update s1 (r 1) (s (r 0) ++ s (r 1))
    have hs0 : s2 (r 0) = s (r 0) := by simp [s2, s1, eqs]
    have hs2 : s2 (r 2) = w := by simp [s2, s1, eqs]
    have hs3 : s2 (r 3) = [] := by simp [s2, s1, eqs, he]
    have hpop := (stack_basic_macros (r 2) s).2.1
    simp only [hs, List.tail_cons] at hpop
    have hcopy := stack_copy (r 0) (r 1) (r 3)
      (neq _ _ (by decide)) (neq _ _ (by decide)) (neq _ _ (by decide)) s1
      (by simp [s1, eqs, he])
    simp only [s1] at hcopy
    simp only [Function.update_of_ne (neq 0 2 (by decide)),
      Function.update_of_ne (neq 1 2 (by decide))] at hcopy
    have hbody := StackProg.Exec.seq hpop hcopy
    have hloop := StackProg.Exec.loopTrue (by simp [hs]) hbody (ih s2 hs2 hs3)
    have hf : Function.update (Function.update s2 (r 2) []) (r 1)
        ((List.replicate w.length (s2 (r 0))).flatten ++ s2 (r 1)) =
        Function.update (Function.update s (r 2) []) (r 1)
        ((List.replicate (a :: w).length (s (r 0))).flatten ++ s (r 1)) := by
      funext k
      by_cases hk : k = r 1
      · subst k
        simp [Function.update, s2, s1, eqs, List.replicate_succ', List.flatten_append, List.append_assoc]
      by_cases hk' : k = r 2
      · subst k; simp [Function.update, eqs]
      · simp [Function.update, s2, s1, hk, hk']
    rw [hf] at hloop
    convert hloop using 1 <;> first | rfl | (simp only [hs0, List.length_cons]; ring)

theorem solution {K A : Type} [DecidableEq K] (r : Fin 4 ↪ K)
    (s : K → List A) (he : s (r 3) = []) :
    (repeatCopyProg r).Exec s
      (Function.update (Function.update s (r 2) []) (r 1)
        ((List.replicate (s (r 2)).length (s (r 0))).flatten ++ s (r 1)))
      ((6 * (s (r 0)).length + 7) * (s (r 2)).length + 1) := by
  exact repeat_copy r (s (r 2)) s rfl he

#print axioms solution
