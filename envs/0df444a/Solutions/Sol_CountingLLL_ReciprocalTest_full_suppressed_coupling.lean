-- Prove2me | solution 1 for CountingLLL.ReciprocalTest.full_suppressed_coupling
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:45:40.460443+00:00
-- url     : https://prove2.me/submissions/cc659dce-3c2c-48a3-ad76-ae25edbf22c6

import Definitions.Def_CountingLLL_ReciprocalAllSuppressed
set_option autoImplicit false
open CountingLLL.ReciprocalTest

private theorem all_step_coupling (ω : Entropy) (s : State) :
    step ω s = allSuppressedStep ω s ∨ (step ω s).phase = .done true := by
  cases hs : s.phase with
  | start => simp only [step, allSuppressedStep, hs]; split <;> simp
  | initialCheck => simp only [step, allSuppressedStep, suppressedStep, hs]; split <;> simp
  | uniformCheck => simp only [step, allSuppressedStep, suppressedStep, hs]; split <;> simp
  | _ => simp [allSuppressedStep, suppressedStep, hs]

/-- On the same entropy tape, the executions coincide until an early return. -/
private theorem all_suppressed_run_coupling (ω : Entropy) (n : ℕ) :
    run ω n = allSuppressedRun ω n ∨ (run ω n).phase = .done true := by
  induction n with
  | zero => left; rfl
  | succ n ih =>
    have hr : run ω (n+1) = step ω (run ω n) := by simp [run, Function.iterate_succ_apply']
    have hs : allSuppressedRun ω (n+1) = allSuppressedStep ω (allSuppressedRun ω n) := by
      simp [allSuppressedRun, Function.iterate_succ_apply']
    rw [hr,hs]
    rcases ih with ih | ih
    · rw [← ih]; exact all_step_coupling ω _
    · right; simp [step,ih]

private theorem all_step_eq_of_safe (ω : Entropy) (s : State)
    (hf : (s.phase = .start ∨ s.phase = .initialCheck) → ω.2.1 s.fairUsed = false)
    (hu : s.phase = .uniformCheck → (ω.2.2 (s.j - 1,s.uniformUsed)).val ≠ 0) :
    step ω s = allSuppressedStep ω s := by
  cases hs : s.phase with
  | start => simp [step, allSuppressedStep, hs, hf (Or.inl hs)]
  | initialCheck => simp [step, allSuppressedStep, suppressedStep, hs, hf (Or.inr hs)]
  | uniformCheck => simp [step, allSuppressedStep, suppressedStep, hs, hu hs]
  | _ => simp [allSuppressedStep, suppressedStep, hs]

/-- Surviving all early checks gives exact synchronization with the paper's full suppressed execution. -/
private theorem all_suppressed_eq_of_checks_survive (ω : Entropy) (n : ℕ)
    (h : ∀ t < n, (((allSuppressedRun ω t).phase = .start ∨ (allSuppressedRun ω t).phase = .initialCheck) → ω.2.1 (allSuppressedRun ω t).fairUsed = false) ∧
      ((allSuppressedRun ω t).phase = .uniformCheck → (ω.2.2 ((allSuppressedRun ω t).j-1,(allSuppressedRun ω t).uniformUsed)).val ≠ 0)) :
    run ω n = allSuppressedRun ω n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hi : run ω n = allSuppressedRun ω n := ih (by intro t ht; exact h t (by omega))
    have ht := h n (by omega)
    have hr : run ω (n+1) = step ω (run ω n) := by simp [run, Function.iterate_succ_apply']
    have hs : allSuppressedRun ω (n+1) = allSuppressedStep ω (allSuppressedRun ω n) := by
      simp [allSuppressedRun, Function.iterate_succ_apply']
    rw [hr, hs, hi]
    exact all_step_eq_of_safe ω _ ht.1 ht.2

/-- Failure of any suppressed early check returns true on the next operational step. -/
private theorem all_suppressed_check_failure_returns (ω : Entropy) (n : ℕ)
    (h : run ω n = allSuppressedRun ω n)
    (hf : (((allSuppressedRun ω n).phase = .start ∨ (allSuppressedRun ω n).phase = .initialCheck) ∧ ω.2.1 (allSuppressedRun ω n).fairUsed = true) ∨
      ((allSuppressedRun ω n).phase = .uniformCheck ∧ (ω.2.2 ((allSuppressedRun ω n).j-1,(allSuppressedRun ω n).uniformUsed)).val = 0)) :
    (run ω (n+1)).phase = .done true := by
  have hr : run ω (n+1) = step ω (run ω n) := by simp [run, Function.iterate_succ_apply']
  rw [hr,h]
  rcases hf with ⟨hp,hv⟩ | ⟨hp,hv⟩
  · rcases hp with hp | hp <;> simp [step,hp,hv]
  · simp [step,hp,hv]

private theorem done_after (ω : Entropy) (n m : ℕ) (b : Bool) (h : (run ω n).phase = .done b) :
    run ω (n+m) = run ω n := by
  have hfixed : step ω (run ω n) = run ω n := by simp [step,h]
  have hi : ∀ m, (step ω)^[m] (run ω n) = run ω n := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => rw [Function.iterate_succ_apply', ih, hfixed]
  change (step ω)^[n+m] initial = _
  rw [Nat.add_comm, Function.iterate_add_apply]
  exact hi m

/-- A false output is exactly absorption of the suppressed execution with every return check survived. -/
private theorem false_output_iff_all_suppressed_survival (ω : Entropy) :
    Returns ω false ↔ ∃ n : ℕ, (allSuppressedRun ω n).phase = .done false ∧
      ∀ t < n, (((allSuppressedRun ω t).phase = .start ∨ (allSuppressedRun ω t).phase = .initialCheck) → ω.2.1 (allSuppressedRun ω t).fairUsed = false) ∧
        ((allSuppressedRun ω t).phase = .uniformCheck → (ω.2.2 ((allSuppressedRun ω t).j-1,(allSuppressedRun ω t).uniformUsed)).val ≠ 0) := by
  constructor
  · rintro ⟨n,hn⟩
    have hnot (t : ℕ) (ht : t ≤ n) : (run ω t).phase ≠ .done true := by
      intro hb
      obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le ht
      rw [hk, done_after ω t k true hb] at hn
      rw [hb] at hn
      contradiction
    have heq (t : ℕ) (ht : t ≤ n) : run ω t = allSuppressedRun ω t := by
      rcases all_suppressed_run_coupling ω t with he | ht'
      · exact he
      · exact (hnot t ht ht').elim
    refine ⟨n, ?_, ?_⟩
    · rw [← heq n (by omega)]; exact hn
    · intro t ht
      constructor
      · intro hp
        cases hb : ω.2.1 (allSuppressedRun ω t).fairUsed with
        | false => rfl
        | true =>
          have hc := all_suppressed_check_failure_returns ω t (heq t (by omega)) (Or.inl ⟨hp,hb⟩)
          exact (hnot (t+1) (by omega) hc).elim
      · intro hp hz
        have hc := all_suppressed_check_failure_returns ω t (heq t (by omega)) (Or.inr ⟨hp,hz⟩)
        exact hnot (t+1) (by omega) hc
  · rintro ⟨n,hn,hsafe⟩
    have he := all_suppressed_eq_of_checks_survive ω n hsafe
    exact ⟨n, by rw [he]; exact hn⟩


theorem solution (ω : Entropy) :
    (∀ n : ℕ, run ω n = allSuppressedRun ω n ∨ (run ω n).phase = .done true) ∧
    (Returns ω false ↔ ∃ n : ℕ, (allSuppressedRun ω n).phase = .done false ∧
      ∀ t < n, (((allSuppressedRun ω t).phase = .start ∨ (allSuppressedRun ω t).phase = .initialCheck) → ω.2.1 (allSuppressedRun ω t).fairUsed = false) ∧
        ((allSuppressedRun ω t).phase = .uniformCheck → (ω.2.2 ((allSuppressedRun ω t).j-1,(allSuppressedRun ω t).uniformUsed)).val ≠ 0)) := by
  exact ⟨all_suppressed_run_coupling ω, false_output_iff_all_suppressed_survival ω⟩
