-- Prove2me | solution 1 for CountingLLL.RevealMachine.fresh_query_probability
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:53:11.472118+00:00
-- url     : https://prove2.me/submissions/bec256ad-e897-40ea-9c5d-8fb829cad518

import Definitions.Def_CountingLLL_RevealMachine
import Theorems.Thm_CountingLLL_RevealMachine_run_depends_on_seen
import Theorems.Thm_CountingLLL_ReciprocalTest_adaptive_fresh_on_event
set_option autoImplicit false
open MeasureTheory ProbabilityTheory CountingLLL.RevealMachine
open scoped ENNReal

/-- Deferred decisions at an atomic step of a deterministic reveal machine. -/
theorem solution {σ ι α : Type*} [Countable ι] [DecidableEq ι]
    [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (P : Program σ ι α) (initial : σ) (n : ℕ) (default : ι) (R : Set σ)
    (κ : ι → Measure α) [∀ i, IsProbabilityMeasure (κ i)]
    (A : ι → Set α) (hA : ∀ i, MeasurableSet (A i)) (p : ℝ≥0∞)
    (hfresh : ∀ ω, (run P ω initial n).1 ∈ R → (P.query (run P ω initial n).1).isSome →
      (P.query (run P ω initial n).1).getD default ∉ (run P ω initial n).2)
    (hsame : ∀ ω, (run P ω initial n).1 ∈ R → (P.query (run P ω initial n).1).isSome →
      κ ((P.query (run P ω initial n).1).getD default) (A ((P.query (run P ω initial n).1).getD default)) = p) :
    (Measure.infinitePi κ) {ω | (run P ω initial n).1 ∈ R ∧ (P.query (run P ω initial n).1).isSome ∧
      ω ((P.query (run P ω initial n).1).getD default) ∈ A ((P.query (run P ω initial n).1).getD default)} =
    (Measure.infinitePi κ) {ω | (run P ω initial n).1 ∈ R ∧ (P.query (run P ω initial n).1).isSome} * p := by
  classical
  let seen : (ι → α) → Finset ι := fun ω => (run P ω initial n).2
  let next : (ι → α) → ι := fun ω => (P.query (run P ω initial n).1).getD default
  let E : Set (ι → α) := {ω | (run P ω initial n).1 ∈ R ∧ (P.query (run P ω initial n).1).isSome}
  have hevent : {ω | (run P ω initial n).1 ∈ R ∧ (P.query (run P ω initial n).1).isSome ∧
      ω ((P.query (run P ω initial n).1).getD default) ∈ A ((P.query (run P ω initial n).1).getD default)} =
      {ω | ω ∈ E ∧ ω (next ω) ∈ A (next ω)} := by
    ext ω; simp [E, next, and_assoc]
  rw [hevent]
  change (Measure.infinitePi κ) {ω | ω ∈ E ∧ ω (next ω) ∈ A (next ω)} = (Measure.infinitePi κ) E * p
  apply CountingLLL.ReciprocalTest.adaptive_fresh_on_event κ A hA p seen next E
  · intro ω hω
    exact hfresh ω hω.1 hω.2
  · intro ω hω
    exact hsame ω hω.1 hω.2
  · intro S a ω ω' h
    constructor
    · rintro ⟨hs, hn⟩
      have heq := run_depends_on_seen P ω ω' initial n (by simpa [seen, hs] using h)
      exact ⟨by simpa [seen, ← heq] using hs, by simpa [next, ← heq] using hn⟩
    · rintro ⟨hs, hn⟩
      have heq := run_depends_on_seen P ω' ω initial n (by
        intro i hi
        exact (h i (by simpa [seen, hs] using hi)).symm)
      exact ⟨by simpa [seen, ← heq] using hs, by simpa [next, ← heq] using hn⟩
  · intro S a ω ω' h hcase
    have heq := run_depends_on_seen P ω ω' initial n (by simpa [seen, hcase.1] using h)
    simp [E, ← heq]
