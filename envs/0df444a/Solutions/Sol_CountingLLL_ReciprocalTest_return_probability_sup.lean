-- Prove2me | solution 1 for CountingLLL.ReciprocalTest.return_probability_sup
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:17:56.225683+00:00
-- url     : https://prove2.me/submissions/1bcfe02e-6b30-45ff-a341-c21f1b7705ba

import Definitions.Def_CountingLLL_ReciprocalTest
set_option autoImplicit false
open MeasureTheory CountingLLL.ReciprocalTest
open scoped ENNReal

private theorem done_fixed (ω : Entropy) (s : State) (b : Bool) (h : s.phase = .done b) : step ω s = s := by
  simp [step, h]

private theorem done_after (ω : Entropy) (n m : ℕ) (b : Bool) (h : (run ω n).phase = .done b) :
    run ω (n+m) = run ω n := by
  have hfixed := done_fixed ω (run ω n) b h
  have hi : ∀ m, (step ω)^[m] (run ω n) = run ω n := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => rw [Function.iterate_succ_apply', ih, hfixed]
  change (step ω)^[n+m] initial = _
  rw [Nat.add_comm, Function.iterate_add_apply]
  exact hi m

/-- The output probability is the supremum of its finite-step done probabilities. -/
theorem solution (B : ℝ≥0∞) (b : Bool) :
    entropyLaw B {ω | Returns ω b} = ⨆ n : ℕ, entropyLaw B {ω | (run ω n).phase = .done b} := by
  let E : ℕ → Set Entropy := fun n => {ω | (run ω n).phase = .done b}
  have hm : Monotone E := by
    intro n m hnm ω hn
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hnm
    change (run ω (n+k)).phase = .done b
    rw [done_after ω n k b hn]
    exact hn
  have heq : {ω | Returns ω b} = ⋃ n, E n := by
    ext ω
    simp [Returns, E]
  rw [heq, hm.measure_iUnion]
