-- Prove2me | solution 1 for CriticalPath.Events.critical_jobs_only_when_earliest
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-28T05:51:39.252173+00:00
-- url     : https://prove2.me/submissions/dea5b20f-11ed-4acf-9e85-b34400592e1f

import Mathlib
import Definitions.Def_CriticalPath_Events_ProjectNetwork
import Definitions.Def_CriticalPath_Events_EventTimes

set_option autoImplicit false

namespace Q0fb

open CriticalPath.Events

theorem earliest_ne {n : ℕ} (N : ProjectNetwork n) (y : Fin (n + 1) → Fin (n + 1) → ℝ)
    {j : Fin (n + 1)} (hj : j ≠ 0) :
    earliest N y j = (N.pred j).attach.sup' (Finset.attach_nonempty_iff.2 (N.pred_nonempty hj))
      (fun i => y i.1 j + earliest N y i.1) := by
  rw [earliest, dif_neg hj]

theorem latest_ne {n : ℕ} (N : ProjectNetwork n) (y : Fin (n + 1) → Fin (n + 1) → ℝ) (lam : ℝ)
    {i : Fin (n + 1)} (hi : i ≠ Fin.last n) :
    latest N y lam i = (N.succ i).attach.inf' (Finset.attach_nonempty_iff.2 (N.succ_nonempty hi))
      (fun j => latest N y lam j.1 - y i j.1) := by
  rw [latest, dif_neg hi]

theorem latest_last {n : ℕ} (N : ProjectNetwork n) (y : Fin (n + 1) → Fin (n + 1) → ℝ)
    (lam : ℝ) : latest N y lam (Fin.last n) = lam := by
  rw [latest, dif_pos rfl]

theorem earliest_ge {n : ℕ} (N : ProjectNetwork n) (y : Fin (n + 1) → Fin (n + 1) → ℝ)
    {i j : Fin (n + 1)} (h : (i, j) ∈ N.P) : y i j + earliest N y i ≤ earliest N y j := by
  have hij : i < j := N.label_lt _ h
  have hj : j ≠ 0 := by
    intro hj
    rw [hj] at hij
    exact absurd hij (Fin.not_lt_zero _)
  rw [earliest_ne N y hj]
  have hi : i ∈ N.pred j := (N.mem_pred).2 h
  exact Finset.le_sup' (fun i : {x // x ∈ N.pred j} => y i.1 j + earliest N y i.1)
    (Finset.mem_attach _ ⟨i, hi⟩)

theorem latest_le {n : ℕ} (N : ProjectNetwork n) (y : Fin (n + 1) → Fin (n + 1) → ℝ) (lam : ℝ)
    {i j : Fin (n + 1)} (h : (i, j) ∈ N.P) : latest N y lam i ≤ latest N y lam j - y i j := by
  have hij : i < j := N.label_lt _ h
  have hi : i ≠ Fin.last n := by
    intro hi
    rw [hi] at hij
    exact absurd hij (not_lt.2 (Fin.le_last _))
  rw [latest_ne N y lam hi]
  have hj : j ∈ N.succ i := (N.mem_succ).2 h
  exact Finset.inf'_le (fun j : {x // x ∈ N.succ i} => latest N y lam j.1 - y i j.1)
    (Finset.mem_attach _ ⟨j, hj⟩)

theorem earliest_attain {n : ℕ} (N : ProjectNetwork n) (y : Fin (n + 1) → Fin (n + 1) → ℝ)
    {j : Fin (n + 1)} (hj : j ≠ 0) :
    ∃ i, (i, j) ∈ N.P ∧ earliest N y j = y i j + earliest N y i := by
  rw [earliest_ne N y hj]
  obtain ⟨⟨i, hi⟩, _, heq⟩ := Finset.exists_mem_eq_sup'
    (Finset.attach_nonempty_iff.2 (N.pred_nonempty hj))
    (fun i : {x // x ∈ N.pred j} => y i.1 j + earliest N y i.1)
  refine ⟨i, (N.mem_pred).1 hi, ?_⟩
  rw [heq]

theorem latest_attain {n : ℕ} (N : ProjectNetwork n) (y : Fin (n + 1) → Fin (n + 1) → ℝ)
    (lam : ℝ) {i : Fin (n + 1)} (hi : i ≠ Fin.last n) :
    ∃ j, (i, j) ∈ N.P ∧ latest N y lam i = latest N y lam j - y i j := by
  rw [latest_ne N y lam hi]
  obtain ⟨⟨j, hj⟩, _, heq⟩ := Finset.exists_mem_eq_inf'
    (Finset.attach_nonempty_iff.2 (N.succ_nonempty hi))
    (fun j : {x // x ∈ N.succ i} => latest N y lam j.1 - y i j.1)
  refine ⟨j, (N.mem_succ).1 hj, ?_⟩
  rw [heq]

theorem slack_nonneg {n : ℕ} (N : ProjectNetwork n) (y : Fin (n + 1) → Fin (n + 1) → ℝ)
    (lam : ℝ) (hlam : earliest N y (Fin.last n) ≤ lam) :
    ∀ k, ∀ i : Fin (n + 1), n - i.val = k → earliest N y i ≤ latest N y lam i := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro i hk
    by_cases hi : i = Fin.last n
    · subst hi
      rw [latest_last]
      exact hlam
    · obtain ⟨j, hP, heq⟩ := latest_attain N y lam hi
      rw [heq]
      have h1 := earliest_ge N y hP
      have hlt : i.val < j.val := N.label_lt _ hP
      have hjle : j.val ≤ n := Fin.is_le j
      have h2 := ih (n - j.val) (by omega) j rfl
      linarith

theorem slack_nonneg' {n : ℕ} (N : ProjectNetwork n) (y : Fin (n + 1) → Fin (n + 1) → ℝ)
    (lam : ℝ) (hlam : earliest N y (Fin.last n) ≤ lam) (i : Fin (n + 1)) :
    earliest N y i ≤ latest N y lam i :=
  slack_nonneg N y lam hlam _ i rfl

/-- The critical-job relation used in `IsCriticalPath`. -/
theorem forward {n : ℕ} (N : ProjectNetwork n) (y : Fin (n + 1) → Fin (n + 1) → ℝ)
    (lam : ℝ) (hlam : earliest N y (Fin.last n) ≤ lam) :
    ∀ k, ∀ v : Fin (n + 1), n - v.val = k → latest N y lam v = earliest N y v →
      lam = earliest N y (Fin.last n) ∧ ∃ q : List (Fin (n + 1)), q.head? = some v ∧
        q.getLast? = some (Fin.last n) ∧
        q.IsChain (fun i j => (i, j) ∈ N.P ∧ IsCritical N y lam (i, j)) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro v hk hv
    by_cases hvl : v = Fin.last n
    · subst hvl
      rw [latest_last] at hv
      exact ⟨hv, [Fin.last n], rfl, rfl, List.IsChain.singleton _⟩
    · obtain ⟨w, hP, heq⟩ := latest_attain N y lam hvl
      have h1 := earliest_ge N y hP
      have h2 := slack_nonneg' N y lam hlam w
      have hw : latest N y lam w = earliest N y w := by linarith
      have hcr : IsCritical N y lam (v, w) := by
        unfold IsCritical maxTimeAvailable
        simp only
        linarith
      have hlt : v.val < w.val := N.label_lt _ hP
      have hwle : w.val ≤ n := Fin.is_le w
      obtain ⟨hl, q, hq1, hq2, hq3⟩ := ih (n - w.val) (by omega) w rfl hw
      obtain ⟨q', rfl⟩ := List.head?_eq_some_iff.1 hq1
      refine ⟨hl, v :: w :: q', rfl, ?_, ?_⟩
      · rw [List.getLast?_cons_cons]
        exact hq2
      · exact List.IsChain.cons_cons ⟨hP, hcr⟩ hq3

theorem backward {n : ℕ} (N : ProjectNetwork n) (y : Fin (n + 1) → Fin (n + 1) → ℝ)
    (lam : ℝ) (hlam : earliest N y (Fin.last n) ≤ lam) :
    ∀ k, ∀ v : Fin (n + 1), v.val = k → latest N y lam v = earliest N y v →
      ∀ q : List (Fin (n + 1)), q.head? = some v → q.getLast? = some (Fin.last n) →
        q.IsChain (fun i j => (i, j) ∈ N.P ∧ IsCritical N y lam (i, j)) →
        ∃ p : List (Fin (n + 1)), IsCriticalPath N y lam p := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro v hk hv q hq1 hq2 hq3
    by_cases hv0 : v = 0
    · subst hv0
      exact ⟨q, hq1, hq2, hq3⟩
    · obtain ⟨u, hP, heq⟩ := earliest_attain N y hv0
      have h1 := latest_le N y lam hP
      have h2 := slack_nonneg' N y lam hlam u
      have hu : latest N y lam u = earliest N y u := by linarith
      have hcr : IsCritical N y lam (u, v) := by
        unfold IsCritical maxTimeAvailable
        simp only
        linarith
      have hlt : u.val < v.val := N.label_lt _ hP
      obtain ⟨q', rfl⟩ := List.head?_eq_some_iff.1 hq1
      refine ih u.val (by omega) u rfl hu (u :: v :: q') rfl ?_ ?_
      · rw [List.getLast?_cons_cons]
        exact hq2
      · exact List.IsChain.cons_cons ⟨hP, hcr⟩ hq3

theorem main {n : ℕ} (N : ProjectNetwork n)
    (y : Fin (n + 1) → Fin (n + 1) → ℝ) (lam : ℝ) (hlam : earliest N y (Fin.last n) ≤ lam)
    (hcrit : ∃ e ∈ N.P, IsCritical N y lam e) :
    lam = earliest N y (Fin.last n) ∧ ∃ p : List (Fin (n + 1)), IsCriticalPath N y lam p := by
  obtain ⟨⟨i, j⟩, hP, hcr⟩ := hcrit
  have hc : latest N y lam j - earliest N y i = y i j := hcr
  have h1 := latest_le N y lam hP
  have h2 := earliest_ge N y hP
  have h3 := slack_nonneg' N y lam hlam i
  have h4 := slack_nonneg' N y lam hlam j
  have hi : latest N y lam i = earliest N y i := by linarith
  have hj : latest N y lam j = earliest N y j := by linarith
  obtain ⟨hl, q, hq1, hq2, hq3⟩ := forward N y lam hlam _ j rfl hj
  refine ⟨hl, ?_⟩
  obtain ⟨q', rfl⟩ := List.head?_eq_some_iff.1 hq1
  refine backward N y lam hlam _ i rfl hi (i :: j :: q') rfl ?_ ?_
  · rw [List.getLast?_cons_cons]
    exact hq2
  · exact List.IsChain.cons_cons ⟨hP, hcr⟩ hq3

end Q0fb

open CriticalPath.Events in
theorem solution {n : ℕ} (N : ProjectNetwork n)
    (y : Fin (n + 1) → Fin (n + 1) → ℝ) (lam : ℝ) (hlam : earliest N y (Fin.last n) ≤ lam)
    (hcrit : ∃ e ∈ N.P, IsCritical N y lam e) :
    lam = earliest N y (Fin.last n) ∧ ∃ p : List (Fin (n + 1)), IsCriticalPath N y lam p := by
  exact Q0fb.main N y lam hlam hcrit
