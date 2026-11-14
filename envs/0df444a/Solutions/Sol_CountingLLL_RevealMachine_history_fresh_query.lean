-- Prove2me | solution 1 for CountingLLL.RevealMachine.history_fresh_query
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:31:50.794178+00:00
-- url     : https://prove2.me/submissions/7af6902a-4e63-4326-a9d9-45e378eb0ba5

import Theorems.Thm_CountingLLL_ReciprocalTest_adaptive_fresh_on_event
import Theorems.Thm_CountingLLL_RevealMachine_run_depends_on_seen
set_option autoImplicit false
open MeasureTheory ProbabilityTheory CountingLLL.RevealMachine
open scoped ENNReal

private theorem seen_step {σ ι α : Type*} [DecidableEq ι] (P : Program σ ι α)
    (ω : ι → α) (c : σ × Finset ι) : c.2 ⊆ (step P ω c).2 := by
  unfold step
  split <;> simp

private theorem seen_mono {σ ι α : Type*} [DecidableEq ι] (P : Program σ ι α)
    (ω : ι → α) (init : σ) {m n : ℕ} (h : m ≤ n) :
    (run P ω init m).2 ⊆ (run P ω init n).2 := by
  induction n with
  | zero =>
    have hm : m = 0 := by omega
    rw [hm]
  | succ n ih =>
    by_cases hm : m ≤ n
    · apply Finset.Subset.trans (ih hm)
      have hh : run P ω init (n+1) = step P ω (run P ω init n) := by
        simp [run, Function.iterate_succ_apply']
      rw [hh]
      exact seen_step P ω _
    · have heq : m = n+1 := by omega
      rw [heq]

private theorem history_eq {σ ι α : Type*} [DecidableEq ι] (P : Program σ ι α)
    (ω ω' : ι → α) (init : σ) (n : ℕ)
    (h : ∀ i ∈ (run P ω init n).2, ω i = ω' i) :
    (fun j : Fin (n+1) => (run P ω init j.val).1) =
      (fun j : Fin (n+1) => (run P ω' init j.val).1) := by
  funext j
  have he := run_depends_on_seen P ω ω' init j.val (fun i hi => h i (seen_mono P ω init (by omega) hi))
  exact congrArg Prod.fst he

/-- A new input remains independent even conditioned on a whole finite execution history. -/
theorem solution {σ ι α : Type*} [Countable ι] [DecidableEq ι]
    [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (P : Program σ ι α) (init : σ) (n : ℕ) (a : ι)
    (H : (Fin (n+1) → σ) → Prop) (κ : ι → Measure α) [∀ i, IsProbabilityMeasure (κ i)]
    (U : Set α) (hU : MeasurableSet U)
    (hfresh : ∀ ω, H (fun j => (run P ω init j.val).1) → P.query (run P ω init n).1 = some a →
      a ∉ (run P ω init n).2) :
    (Measure.infinitePi κ) {ω | H (fun j => (run P ω init j.val).1) ∧
      P.query (run P ω init n).1 = some a ∧ ω a ∈ U} =
      (Measure.infinitePi κ) {ω | H (fun j => (run P ω init j.val).1) ∧
      P.query (run P ω init n).1 = some a} * κ a U := by
  classical
  let seen : (ι → α) → Finset ι := fun ω => (run P ω init n).2
  let E : Set (ι → α) := {ω | H (fun j => (run P ω init j.val).1) ∧ P.query (run P ω init n).1 = some a}
  have h := CountingLLL.ReciprocalTest.adaptive_fresh_on_event κ (fun _ => U) (fun _ => hU) (κ a U) seen (fun _ => a) E
    (by intro ω hω; exact hfresh ω hω.1 hω.2)
    (by intro ω hω; rfl)
    (by
      intro S b ω ω' he
      constructor
      · rintro ⟨hs,hb⟩
        have hrun := run_depends_on_seen P ω ω' init n (by simpa [seen, hs] using he)
        exact ⟨by simpa [seen, ← hrun] using hs, hb⟩
      · rintro ⟨hs,hb⟩
        have hrun := run_depends_on_seen P ω' ω init n (by intro i hi; exact (he i (by simpa [seen, hs] using hi)).symm)
        exact ⟨by simpa [seen, ← hrun] using hs, hb⟩)
    (by
      intro S b ω ω' he hcase
      have hrun := run_depends_on_seen P ω ω' init n (by simpa [seen, hcase.1] using he)
      have hhist := history_eq P ω ω' init n (by simpa [seen, hcase.1] using he)
      simp only [E, Set.mem_setOf_eq, hhist, hrun])
  simpa [E, and_assoc] using h
