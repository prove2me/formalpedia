-- Prove2me | solution 1 for CriticalPath.Events.earliest_isLeast
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-28T00:01:46.557026+00:00
-- url     : https://prove2.me/submissions/e5db5afd-7dc8-4c8f-895a-103fe8c93c35

import Mathlib
import Definitions.Def_CriticalPath_Events_ProjectNetwork
import Definitions.Def_CriticalPath_Events_EventTimes

open CriticalPath.Events

theorem solution {n : ℕ} (N : ProjectNetwork n) (y : Fin (n + 1) → Fin (n + 1) → ℝ) :
    IsLeast {t : Fin (n + 1) → ℝ | t 0 = 0 ∧ ∀ e ∈ N.P, y e.1 e.2 ≤ t e.2 - t e.1}
      (earliest N y) := by
  have hzero : earliest N y 0 = 0 := by
    rw [earliest]
    simp
  have hunfold : ∀ (j : Fin (n + 1)) (hj : j ≠ 0),
      earliest N y j = (N.pred j).attach.sup'
        (Finset.attach_nonempty_iff.2 (N.pred_nonempty hj))
        (fun i => y i.1 j + earliest N y i.1) := by
    intro j hj
    rw [earliest, dif_neg hj]
  constructor
  · refine ⟨hzero, ?_⟩
    rintro ⟨i, j⟩ hij
    have hji : i < j := N.label_lt (i, j) hij
    have hj0 : j ≠ 0 := by
      intro h
      rw [h] at hji
      simp at hji
    have hmem : i ∈ N.pred j := (N.mem_pred).2 hij
    have hle : y i j + earliest N y i ≤ earliest N y j := by
      rw [hunfold j hj0]
      exact Finset.le_sup' (fun k : {x // x ∈ N.pred j} => y k.1 j + earliest N y k.1)
        (Finset.mem_attach _ ⟨i, hmem⟩)
    show y i j ≤ earliest N y j - earliest N y i
    linarith
  · rintro t ⟨ht0, htP⟩
    have key : ∀ m : ℕ, ∀ j : Fin (n + 1), j.val = m → earliest N y j ≤ t j := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m ih =>
        intro j hj
        by_cases hj0 : j = 0
        · rw [hj0, hzero, ht0]
        · rw [hunfold j hj0]
          refine Finset.sup'_le _ _ ?_
          rintro ⟨i, hi⟩ -
          have hlt : i < j := N.lt_of_mem_pred hi
          have hiv : i.val < m := by
            rw [← hj]
            exact hlt
          have hind : earliest N y i ≤ t i := ih i.val hiv i rfl
          have hedge : y i j ≤ t j - t i := htP (i, j) ((N.mem_pred).1 hi)
          show y i j + earliest N y i ≤ t j
          linarith
    intro j
    exact key j.val j rfl
