-- Prove2me | solution 1 for CriticalPath.Events.latest_isGreatest
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-28T02:02:07.771974+00:00
-- url     : https://prove2.me/submissions/ed1179b7-6427-4705-9ba4-9fbbd6106fac

import Mathlib
import Definitions.Def_CriticalPath_Events_ProjectNetwork
import Definitions.Def_CriticalPath_Events_EventTimes

open CriticalPath.Events

theorem solution {n : ℕ} (N : ProjectNetwork n) (y : Fin (n + 1) → Fin (n + 1) → ℝ)
    (lam : ℝ) (hlam : earliest N y (Fin.last n) ≤ lam) :
    latest N y lam (Fin.last n) = lam ∧
      IsGreatest {t : Fin (n + 1) → ℝ | t (Fin.last n) ≤ lam ∧
          ∀ e ∈ N.P, y e.1 e.2 ≤ t e.2 - t e.1}
        (latest N y lam) := by
  have hlast : latest N y lam (Fin.last n) = lam := by
    rw [latest]; simp
  have hunfold : ∀ (i : Fin (n + 1)) (hi : i ≠ Fin.last n),
      latest N y lam i = (N.succ i).attach.inf'
        (Finset.attach_nonempty_iff.2 (N.succ_nonempty hi))
        (fun j => latest N y lam j.1 - y i j.1) := by
    intro i hi
    rw [latest, dif_neg hi]
  refine ⟨hlast, ⟨⟨by rw [hlast], ?_⟩, ?_⟩⟩
  · rintro ⟨i, j⟩ hij
    have hji : i < j := N.label_lt (i, j) hij
    have hi : i ≠ Fin.last n := by
      intro h
      rw [h] at hji
      exact absurd (Fin.le_last j) (not_le.mpr hji)
    have hmem : j ∈ N.succ i := (N.mem_succ).2 hij
    have hle : latest N y lam i ≤ latest N y lam j - y i j := by
      rw [hunfold i hi]
      exact Finset.inf'_le (fun k : {x // x ∈ N.succ i} => latest N y lam k.1 - y i k.1)
        (Finset.mem_attach _ ⟨j, hmem⟩)
    show y i j ≤ latest N y lam j - latest N y lam i
    linarith
  · rintro t ⟨htlast, htP⟩
    have key : ∀ m : ℕ, ∀ i : Fin (n + 1), n - i.val = m → t i ≤ latest N y lam i := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m ih =>
        intro i him
        by_cases hlast' : i = Fin.last n
        · rw [hlast', hlast]
          rw [hlast'] at *
          exact htlast
        · rw [hunfold i hlast']
          refine Finset.le_inf' _ _ ?_
          rintro ⟨j, hj⟩ -
          have hlt : i < j := N.lt_of_mem_succ hj
          have hjv : n - j.val < m := by
            rw [← him]
            have h1 : i.val < j.val := hlt
            have h2 : j.val ≤ n := Nat.lt_succ_iff.mp j.isLt
            omega
          have hind : t j ≤ latest N y lam j := ih (n - j.val) hjv j rfl
          have hedge : y i j ≤ t j - t i := htP (i, j) ((N.mem_succ).1 hj)
          show t i ≤ latest N y lam j - y i j
          linarith
    intro i
    exact key (n - i.val) i rfl
