-- Prove2me | solution 1 for CookPvsNP.stack_sync_pop
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T14:04:00.286214+00:00
-- url     : https://prove2.me/submissions/10b2aa6f-21dc-46d7-a808-dd1b15c829dc

import Definitions.Def_CookPvsNP_StackCompare

set_option autoImplicit false
open CookPvsNP

private theorem sync_pop {K A : Type} [DecidableEq K] (i j : K) (hne : i ≠ j)
    (w v : List A) (s : K → List A) (hi : s i = w) (hj : s j = v) :
    (syncPopProg i j).Exec s
      (Function.update (Function.update s i (w.drop (min w.length v.length))) j
        (v.drop (min w.length v.length))) (3 * min w.length v.length + 1) := by
  induction w generalizing s v with
  | nil =>
    simp only [List.length_nil, Nat.zero_min, List.drop_zero, Nat.mul_zero, Nat.zero_add]
    have hf : Function.update (Function.update s i []) j v = s := by
      rw [← hi, Function.update_eq_self, ← hj, Function.update_eq_self]
    rw [hf]
    exact .loopFalse (by simp [hi])
  | cons a w ih =>
    cases v with
    | nil =>
      simp only [List.length_nil, Nat.min_zero, List.drop_zero, Nat.mul_zero, Nat.zero_add]
      have hf : Function.update (Function.update s i (a :: w)) j [] = s := by
        rw [← hi, Function.update_eq_self, ← hj, Function.update_eq_self]
      rw [hf]
      exact .loopFalse (by simp [hj])
    | cons b v =>
      let s' := StackProg.applyAct (syncPopAct i j) s
      have hi' : s' i = w := by simp [s', StackProg.applyAct, syncPopAct, StackAct.apply, hi]
      have hj' : s' j = v := by simp [s', StackProg.applyAct, syncPopAct, StackAct.apply, hj]
      have he := StackProg.Exec.loopTrue (by simp [hi, hj])
        (StackProg.Exec.act (syncPopAct i j) s) (ih v s' hi' hj')
      have hf : Function.update (Function.update s' i (w.drop (min w.length v.length))) j
          (v.drop (min w.length v.length)) =
          Function.update (Function.update s i ((a :: w).drop (min (a :: w).length (b :: v).length))) j
          ((b :: v).drop (min (a :: w).length (b :: v).length)) := by
        funext k
        by_cases hk : k = i
        · subst k; simp [Function.update, hne]
        by_cases hk' : k = j
        · subst k; simp [Function.update]
        · simp [Function.update, hk, hk', s', StackProg.applyAct, syncPopAct, StackAct.apply]
      rw [hf] at he
      convert he using 1 <;> first | rfl | (simp; omega)

theorem solution {K A : Type} [DecidableEq K] (i j : K) (hne : i ≠ j) (s : K → List A) :
    let m := min (s i).length (s j).length
    (syncPopProg i j).Exec s (Function.update (Function.update s i ((s i).drop m)) j ((s j).drop m))
      (3 * m + 1) := by
  exact sync_pop i j hne (s i) (s j) s rfl rfl

#print axioms solution
