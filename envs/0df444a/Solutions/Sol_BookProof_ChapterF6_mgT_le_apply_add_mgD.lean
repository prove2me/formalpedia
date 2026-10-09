-- Prove2me | solution 1 for BookProof.ChapterF6.mgT_le_apply_add_mgD
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:05:33.106206+00:00
-- url     : https://prove2.me/submissions/2fe9ae4f-b961-4268-bf37-57f2860522b0

-- Generated from ChapterF6.lean — solution of BookProof.ChapterF6.mgT_le_apply_add_mgD
import Mathlib
import Definitions.Def_ChapterF6
import Theorems.Thm_BookProof_ChapterF6_mgT_cons
import Theorems.Thm_BookProof_ChapterF6_mgStep_le_apply_add
import Theorems.Thm_BookProof_ChapterF6_mgD_cons
open BookProof.ChapterF6



open scoped BigOperators


variable {α : Type*} [DecidableEq α]

variable {α : Type*} [DecidableEq α]

set_option maxHeartbeats 1000000 in
theorem solution (k : ℕ) (T : α →₀ ℕ) (s : List α) (y : α) :
    T y + s.count y ≤ (mgT k T s) y + mgD k T s := by

  induction s using List.reverseRecOn generalizing T y with
  | nil => ?_
  | append_singleton s x ih => ?_
  · simp [mgT, mgD]
  · have h_step : ∀ (T' : α →₀ ℕ) (l : List α),
        mgD k T' (l ++ [x]) = mgD k T' l + (if 0 < (mgT k T' l) x
          ∨ (mgT k T' l).support.card < k then 0 else 1) := by
      intro T' l
      induction l generalizing T' with
      | nil => simp [mgD, mgT]; rfl
      | cons z zs ih =>
        simp only [List.cons_append, mgD_cons, mgT_cons]
        rw [ih]
        ring
    have hcount : List.count y (s ++ [x]) = List.count y s + if x = y then 1 else 0 := by
      rw [List.count_append, List.count_singleton]
      by_cases h : x = y <;> simp [h]
    have hT : mgT k T (s ++ [x]) = mgStep k (mgT k T s) x := by
      simp [mgT, List.foldl_append]
    have hstep := mgStep_le_apply_add k (mgT k T s) x y
    have hih := ih T y
    have heq : (if x = y then 1 else 0 : ℕ) = if y = x then 1 else 0 := by
      by_cases h : x = y <;> simp [h, eq_comm]
    rw [hcount, h_step, hT, heq]
    omega
