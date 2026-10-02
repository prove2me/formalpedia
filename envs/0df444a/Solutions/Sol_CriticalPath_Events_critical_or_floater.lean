-- Prove2me | solution 1 for CriticalPath.Events.critical_or_floater
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T15:08:29.757401+00:00
-- url     : https://prove2.me/submissions/5a1199fd-467d-4710-8832-ac764d8ae1dd

import Mathlib
import Definitions.Def_CriticalPath_Events_ProjectNetwork
import Definitions.Def_CriticalPath_Events_EventTimes

set_option autoImplicit false

open CriticalPath.Events in
theorem cof_earliest_ge {n : ℕ} (N : ProjectNetwork n) (y : Fin (n + 1) → Fin (n + 1) → ℝ)
    {i j : Fin (n + 1)} (h : (i, j) ∈ N.P) :
    y i j + earliest N y i ≤ earliest N y j := by
  have hlt : i < j := N.label_lt (i, j) h
  have hj : j ≠ 0 := by
    intro h0
    rw [h0] at hlt
    exact absurd hlt (Fin.not_lt_zero i)
  conv_rhs => rw [earliest]
  rw [dif_neg hj]
  exact Finset.le_sup' (fun i' : {x // x ∈ N.pred j} => y i'.1 j + earliest N y i'.1)
    (b := ⟨i, (N.mem_pred).2 h⟩) (Finset.mem_attach _ _)

open CriticalPath.Events in
theorem cof_latest_le {n : ℕ} (N : ProjectNetwork n) (y : Fin (n + 1) → Fin (n + 1) → ℝ)
    (lam : ℝ) {i j : Fin (n + 1)} (h : (i, j) ∈ N.P) :
    latest N y lam i ≤ latest N y lam j - y i j := by
  have hlt : i < j := N.label_lt (i, j) h
  have hi : i ≠ Fin.last n := by
    intro h0
    rw [h0] at hlt
    exact absurd hlt (not_lt.2 (Fin.le_last j))
  conv_lhs => rw [latest]
  rw [dif_neg hi]
  exact Finset.inf'_le (fun j' : {x // x ∈ N.succ i} => latest N y lam j'.1 - y i j'.1)
    (b := ⟨j, (N.mem_succ).2 h⟩) (Finset.mem_attach _ _)

open CriticalPath.Events in
theorem cof_earliest_le_latest {n : ℕ} (N : ProjectNetwork n)
    (y : Fin (n + 1) → Fin (n + 1) → ℝ) (lam : ℝ) (hlam : earliest N y (Fin.last n) ≤ lam) :
    ∀ m : ℕ, ∀ k : Fin (n + 1), n - k.val = m → earliest N y k ≤ latest N y lam k := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro k hk
    by_cases hkl : k = Fin.last n
    · subst hkl
      rw [latest, dif_pos rfl]
      exact hlam
    · conv_rhs => rw [latest]
      rw [dif_neg hkl]
      apply Finset.le_inf'
      intro j _
      have hP : (k, j.1) ∈ N.P := (N.mem_succ).1 j.2
      have hlt : k < j.1 := N.label_lt _ hP
      have hlt' : k.val < j.1.val := hlt
      have hle : j.1.val ≤ n := Nat.lt_succ_iff.1 j.1.is_lt
      have h1 := cof_earliest_ge N y hP
      have h2 := ih (n - j.1.val) (by omega) j.1 rfl
      linarith

open CriticalPath.Events in
theorem solution {n : ℕ} (N : ProjectNetwork n) (y : Fin (n + 1) → Fin (n + 1) → ℝ)
    (lam : ℝ) (hlam : earliest N y (Fin.last n) ≤ lam) :
    (∀ i, earliest N y i ≤ latest N y lam i) ∧
      ∀ e ∈ N.P, IsCritical N y lam e ∨ IsFloater N y lam e := by
  have H : ∀ i, earliest N y i ≤ latest N y lam i :=
    fun i => cof_earliest_le_latest N y lam hlam _ i rfl
  refine ⟨H, ?_⟩
  rintro ⟨i, j⟩ h
  have h1 := cof_earliest_ge N y h
  have h2 := H j
  have hle : y i j ≤ maxTimeAvailable N y lam (i, j) := by
    unfold maxTimeAvailable
    simp only
    linarith
  rcases hle.eq_or_lt with heq | hlt
  · left
    exact heq.symm
  · right
    exact hlt
