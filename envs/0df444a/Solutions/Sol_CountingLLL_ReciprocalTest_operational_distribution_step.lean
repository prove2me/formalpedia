-- Prove2me | solution 1 for CountingLLL.ReciprocalTest.operational_distribution_step
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:17:55.510246+00:00
-- url     : https://prove2.me/submissions/5d9f627d-46aa-4f99-9159-4ec17d99c437

import Definitions.Def_CountingLLL_ReciprocalTransition
import Theorems.Thm_CountingLLL_ReciprocalTest_operational_transition_law
import Theorems.Thm_CountingLLL_ReciprocalTest_operational_silent_transition
import Theorems.Thm_CountingLLL_ReciprocalTest_reciprocal_reveal_simulates
import Theorems.Thm_CountingLLL_RevealMachine_run_depends_on_seen
set_option autoImplicit false
open MeasureTheory ProbabilityTheory CountingLLL.ReciprocalTest CountingLLL.RevealMachine
open scoped ENNReal

deriving instance Encodable for Context
deriving instance Encodable for Phase
deriving instance Encodable for State

private theorem finite_dep_meas (S : Finset ReadIndex) (E : Set (ReadIndex → ℕ))
    (hE : ∀ ω ω', (∀ i ∈ S, ω i = ω' i) → (ω ∈ E ↔ ω' ∈ E)) : MeasurableSet E := by
  classical
  let f : (ReadIndex → ℕ) → (S → ℕ) := fun ω j => ω j
  have hf : Measurable f := measurable_pi_lambda _ (fun j => measurable_pi_apply j.val)
  let F : Set (S → ℕ) := {x | ∃ ω : ReadIndex → ℕ, f ω = x ∧ ω ∈ E}
  have heq : f ⁻¹' F = E := by
    ext ω
    constructor
    · rintro ⟨ω', heq, hn⟩
      apply (hE ω ω' ?_).2 hn
      intro i hi
      exact (congrFun heq ⟨i,hi⟩).symm
    · intro hn; exact ⟨ω, rfl, hn⟩
  rw [← heq]
  exact (Set.to_countable F).measurableSet.preimage hf

private theorem state_event_meas (n : ℕ) (s : State) :
    MeasurableSet {x : ReadIndex → ℕ | (CountingLLL.RevealMachine.run revealProgram x initial n).1 = s} := by
  let C : Finset ReadIndex → Set (ReadIndex → ℕ) := fun S =>
    {x | (CountingLLL.RevealMachine.run revealProgram x initial n).1 = s ∧
      (CountingLLL.RevealMachine.run revealProgram x initial n).2 = S}
  have hc (S : Finset ReadIndex) : MeasurableSet (C S) := by
    apply finite_dep_meas S (C S)
    intro x y h
    constructor
    · rintro ⟨hstate,hseen⟩
      have heq := run_depends_on_seen revealProgram x y initial n (by simpa [hseen] using h)
      exact ⟨by simpa [← heq] using hstate, by simpa [← heq] using hseen⟩
    · rintro ⟨hstate,hseen⟩
      have heq := run_depends_on_seen revealProgram y x initial n (by
        intro i hi; exact (h i (by simpa [hseen] using hi)).symm)
      exact ⟨by simpa [← heq] using hstate, by simpa [← heq] using hseen⟩
  have heq : {x : ReadIndex → ℕ | (CountingLLL.RevealMachine.run revealProgram x initial n).1 = s} = ⋃ S, C S := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro hs; exact ⟨(CountingLLL.RevealMachine.run revealProgram x initial n).2, hs, rfl⟩
    · rintro ⟨S,hs,hS⟩; exact hs
  rw [heq]
  exact MeasurableSet.iUnion hc

private theorem code_meas : Measurable entropyCode := by
  apply measurable_pi_lambda
  intro a
  cases a with
  | inl i =>
    change Measurable (fun ω : Entropy => if ω.1 i then (1:ℕ) else 0)
    exact (measurable_of_countable bitCode).comp ((measurable_pi_apply i).comp measurable_fst)
  | inr a =>
    cases a with
    | inl i =>
      change Measurable (fun ω : Entropy => if ω.2.1 i then (1:ℕ) else 0)
      exact (measurable_of_countable bitCode).comp ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd))
    | inr a =>
      change Measurable (fun ω : Entropy => (ω.2.2 a).val)
      exact (measurable_of_countable (fun x : Fin (a.1+1) => x.val)).comp
        ((measurable_pi_apply a).comp (measurable_snd.comp measurable_snd))


private theorem operational_state_meas (n : ℕ) (s : State) :
    MeasurableSet {ω : Entropy | CountingLLL.ReciprocalTest.run ω n = s} := by
  have hm := (state_event_meas n s).preimage code_meas
  have heq : entropyCode ⁻¹' {x | (CountingLLL.RevealMachine.run revealProgram x initial n).1 = s} =
      {ω | CountingLLL.ReciprocalTest.run ω n = s} := by
    ext ω
    change (CountingLLL.RevealMachine.run revealProgram (entropyCode ω) initial n).1 = s ↔ _
    rw [reciprocal_reveal_simulates]
    rfl
  simpa only [heq] using hm

/-- Full one-step countable-state distribution recursion for the original machine. -/
theorem solution (B : ℝ≥0∞) (hB : B ≤ 1) (n : ℕ) (s' : State) :
    entropyLaw B {ω | CountingLLL.ReciprocalTest.run ω (n+1) = s'} =
      ∑' s : State, entropyLaw B {ω | CountingLLL.ReciprocalTest.run ω n = s} * transitionMass B s s' := by
  classical
  let E : State → Set Entropy := fun s => {ω | CountingLLL.ReciprocalTest.run ω n = s ∧
      CountingLLL.ReciprocalTest.run ω (n+1) = s'}
  have hEmeas (s : State) : MeasurableSet (E s) :=
    (operational_state_meas n s).inter (operational_state_meas (n+1) s')
  have hEdisj : Pairwise (fun s t => Disjoint (E s) (E t)) := by
    intro s t hst
    apply Set.disjoint_left.mpr
    intro ω hs ht
    exact hst (hs.1.symm.trans ht.1)
  have hEcover : (⋃ s, E s) = {ω | CountingLLL.ReciprocalTest.run ω (n+1) = s'} := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · rintro ⟨s,hs,ht⟩; exact ht
    · intro ht; exact ⟨CountingLLL.ReciprocalTest.run ω n, rfl, ht⟩
  have hterm (s : State) : entropyLaw B (E s) =
      entropyLaw B {ω | CountingLLL.ReciprocalTest.run ω n = s} * transitionMass B s s' := by
    cases hq : readIndex s with
    | none =>
      have hs := operational_silent_transition B n s s' hq
      by_cases hnext : step (uniformEntropy 0) s = s'
      · simpa [E, transitionMass, hq, hnext] using hs.1 hnext
      · simpa [E, transitionMass, hq, hnext] using hs.2 hnext
    | some a =>
      simpa [E, transitionMass, hq] using operational_transition_law B hB n s s' a hq
  calc
    _ = entropyLaw B (⋃ s, E s) := by rw [hEcover]
    _ = ∑' s, entropyLaw B (E s) := measure_iUnion hEdisj hEmeas
    _ = _ := by simp_rw [hterm]
