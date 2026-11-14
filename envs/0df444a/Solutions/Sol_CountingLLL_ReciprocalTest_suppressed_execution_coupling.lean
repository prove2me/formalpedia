-- Prove2me | solution 1 for CountingLLL.ReciprocalTest.suppressed_execution_coupling
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:41:34.059136+00:00
-- url     : https://prove2.me/submissions/bee1b441-d994-4d40-a968-b82ab8df3125

import Definitions.Def_CountingLLL_ReciprocalSuppressed
set_option autoImplicit false
open CountingLLL.ReciprocalTest

private theorem step_coupling (ω : Entropy) (s : State) :
    step ω s = suppressedStep ω s ∨ (step ω s).phase = .done true := by
  cases hs : s.phase with
  | initialCheck =>
    simp only [step, suppressedStep, hs]
    split <;> simp
  | uniformCheck =>
    simp only [step, suppressedStep, hs]
    split <;> simp
  | _ => simp [suppressedStep, hs]

private theorem suppressed_run_coupling (ω : Entropy) (n : ℕ) :
    run ω n = suppressedRun ω n ∨ (run ω n).phase = .done true := by
  induction n with
  | zero => left; rfl
  | succ n ih =>
    have hr : run ω (n+1) = step ω (run ω n) := by simp [run, Function.iterate_succ_apply']
    have hs : suppressedRun ω (n+1) = suppressedStep ω (suppressedRun ω n) := by
      simp [suppressedRun, Function.iterate_succ_apply']
    rw [hr,hs]
    rcases ih with ih | ih
    · rw [← ih]
      exact step_coupling ω _
    · right
      simp [step,ih]

private theorem step_eq_of_safe (ω : Entropy) (s : State)
    (hf : s.phase = .initialCheck → ω.2.1 s.fairUsed = false)
    (hu : s.phase = .uniformCheck → (ω.2.2 (s.j - 1,s.uniformUsed)).val ≠ 0) :
    step ω s = suppressedStep ω s := by
  cases hs : s.phase with
  | initialCheck => simp [step, suppressedStep, hs, hf hs]
  | uniformCheck => simp [step, suppressedStep, hs, hu hs]
  | _ => simp [suppressedStep, hs]

/-- All suppressed checks up to time n surviving gives exact synchronization. -/
private theorem suppressed_run_eq_of_checks_survive (ω : Entropy) (n : ℕ)
    (h : ∀ t < n, ((suppressedRun ω t).phase = .initialCheck → ω.2.1 (suppressedRun ω t).fairUsed = false) ∧
      ((suppressedRun ω t).phase = .uniformCheck → (ω.2.2 ((suppressedRun ω t).j-1,(suppressedRun ω t).uniformUsed)).val ≠ 0)) :
    run ω n = suppressedRun ω n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hi : run ω n = suppressedRun ω n := ih (by intro t ht; exact h t (by omega))
    have ht := h n (by omega)
    have hr : run ω (n+1) = step ω (run ω n) := by simp [run, Function.iterate_succ_apply']
    have hs : suppressedRun ω (n+1) = suppressedStep ω (suppressedRun ω n) := by
      simp [suppressedRun, Function.iterate_succ_apply']
    rw [hr, hs, hi]
    exact step_eq_of_safe ω _ ht.1 ht.2

/-- The first check failed while synchronized returns true on the next step. -/
private theorem suppressed_check_failure_returns (ω : Entropy) (n : ℕ)
    (h : run ω n = suppressedRun ω n)
    (hf : ((suppressedRun ω n).phase = .initialCheck ∧ ω.2.1 (suppressedRun ω n).fairUsed = true) ∨
      ((suppressedRun ω n).phase = .uniformCheck ∧ (ω.2.2 ((suppressedRun ω n).j-1,(suppressedRun ω n).uniformUsed)).val = 0)) :
    (run ω (n+1)).phase = .done true := by
  have hr : run ω (n+1) = step ω (run ω n) := by simp [run, Function.iterate_succ_apply']
  rw [hr,h]
  rcases hf with ⟨hp,hv⟩ | ⟨hp,hv⟩ <;> simp [step,hp,hv]

private theorem suppressed_step_ext (ω ω' : Entropy) (s : State)
    (ho : ω.1 = ω'.1) (hf : ω.2.1 = ω'.2.1) :
    suppressedStep ω s = suppressedStep ω' s := by
  cases hp : s.phase <;> simp [suppressedStep, step, hp, ho, hf]

/-- The suppressed trajectory never depends on the uniform-check entropy. -/
private theorem suppressed_run_ignores_uniform (ω ω' : Entropy)
    (ho : ω.1 = ω'.1) (hf : ω.2.1 = ω'.2.1) (n : ℕ) :
    suppressedRun ω n = suppressedRun ω' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hr (ξ : Entropy) : suppressedRun ξ (n+1) = suppressedStep ξ (suppressedRun ξ n) := by
      simp [suppressedRun, Function.iterate_succ_apply']
    rw [hr,hr,ih]
    exact suppressed_step_ext ω ω' _ ho hf

/-- Pathwise coupling of the real and suppressed executions. -/
theorem solution :
    (∀ ω : Entropy, ∀ n : ℕ, run ω n = suppressedRun ω n ∨ (run ω n).phase = .done true) ∧
    (∀ (ω : Entropy) (n : ℕ),
      (∀ t < n, ((suppressedRun ω t).phase = .initialCheck → ω.2.1 (suppressedRun ω t).fairUsed = false) ∧
        ((suppressedRun ω t).phase = .uniformCheck → (ω.2.2 ((suppressedRun ω t).j-1,(suppressedRun ω t).uniformUsed)).val ≠ 0)) →
      run ω n = suppressedRun ω n) ∧
    (∀ (ω : Entropy) (n : ℕ), run ω n = suppressedRun ω n →
      (((suppressedRun ω n).phase = .initialCheck ∧ ω.2.1 (suppressedRun ω n).fairUsed = true) ∨
       ((suppressedRun ω n).phase = .uniformCheck ∧ (ω.2.2 ((suppressedRun ω n).j-1,(suppressedRun ω n).uniformUsed)).val = 0)) →
      (run ω (n+1)).phase = .done true) ∧
    (∀ (ω ω' : Entropy), ω.1 = ω'.1 → ω.2.1 = ω'.2.1 → ∀ n : ℕ,
      suppressedRun ω n = suppressedRun ω' n) := by
  exact ⟨suppressed_run_coupling, suppressed_run_eq_of_checks_survive,
    suppressed_check_failure_returns, suppressed_run_ignores_uniform⟩
