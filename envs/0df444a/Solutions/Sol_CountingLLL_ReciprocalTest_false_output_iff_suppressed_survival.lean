-- Prove2me | solution 1 for CountingLLL.ReciprocalTest.false_output_iff_suppressed_survival
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:42:47.443198+00:00
-- url     : https://prove2.me/submissions/749b1adc-40f1-476e-bab5-7c593a1c1c40

import Theorems.Thm_CountingLLL_ReciprocalTest_suppressed_execution_coupling
set_option autoImplicit false
open CountingLLL.ReciprocalTest

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
theorem solution (ω : Entropy) :
    Returns ω false ↔ ∃ n : ℕ, (suppressedRun ω n).phase = .done false ∧
      ∀ t < n, ((suppressedRun ω t).phase = .initialCheck → ω.2.1 (suppressedRun ω t).fairUsed = false) ∧
        ((suppressedRun ω t).phase = .uniformCheck → (ω.2.2 ((suppressedRun ω t).j-1,(suppressedRun ω t).uniformUsed)).val ≠ 0) := by
  constructor
  · rintro ⟨n,hn⟩
    have hnot (t : ℕ) (ht : t ≤ n) : (run ω t).phase ≠ .done true := by
      intro hb
      obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le ht
      rw [hk, done_after ω t k true hb] at hn
      rw [hb] at hn
      contradiction
    have heq (t : ℕ) (ht : t ≤ n) : run ω t = suppressedRun ω t := by
      rcases (suppressed_execution_coupling.1 ω t) with he | ht'
      · exact he
      · exact (hnot t ht ht').elim
    refine ⟨n, ?_, ?_⟩
    · rw [← heq n (by omega)]; exact hn
    · intro t ht
      constructor
      · intro hp
        cases hb : ω.2.1 (suppressedRun ω t).fairUsed with
        | false => rfl
        | true =>
          have hc := (suppressed_execution_coupling.2.2.1 ω t) (heq t (by omega)) (Or.inl ⟨hp,hb⟩)
          exact (hnot (t+1) (by omega) hc).elim
      · intro hp hz
        have hc := (suppressed_execution_coupling.2.2.1 ω t) (heq t (by omega)) (Or.inr ⟨hp,hz⟩)
        exact hnot (t+1) (by omega) hc
  · rintro ⟨n,hn,hsafe⟩
    have he := (suppressed_execution_coupling.2.1 ω n) hsafe
    exact ⟨n, by rw [he]; exact hn⟩
