-- Prove2me | solution 1 for CountingLLL.ReciprocalTest.operational_query_fresh
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:11:22.1682+00:00
-- url     : https://prove2.me/submissions/4e73fae5-1c4f-49f3-8e71-6642c6420aca

import Definitions.Def_CountingLLL_ReciprocalEncodedLaw
import Theorems.Thm_CountingLLL_ReciprocalTest_entropyCode_law
import Theorems.Thm_CountingLLL_ReciprocalTest_encoded_query_fresh
import Theorems.Thm_CountingLLL_ReciprocalTest_reciprocal_reveal_simulates
import Theorems.Thm_CountingLLL_RevealMachine_run_depends_on_seen
set_option autoImplicit false
open MeasureTheory ProbabilityTheory CountingLLL.ReciprocalTest CountingLLL.RevealMachine
open scoped ENNReal

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

/-- The next operational entropy value is fresh even after conditioning on the exact state. -/
theorem solution (B : ℝ≥0∞) (hB : B ≤ 1) (n : ℕ) (s : State) (a : ReadIndex)
    (ha : readIndex s = some a) (U : Set ℕ) :
    entropyLaw B {ω | CountingLLL.ReciprocalTest.run ω n = s ∧ entropyCode ω a ∈ U} =
      entropyLaw B {ω | CountingLLL.ReciprocalTest.run ω n = s} * readLaw B a U := by
  let E : Set (ReadIndex → ℕ) := {x | (CountingLLL.RevealMachine.run revealProgram x initial n).1 = s}
  let F : Set (ReadIndex → ℕ) := E ∩ {x | x a ∈ U}
  have hE : MeasurableSet E := state_event_meas n s
  have hF : MeasurableSet F := hE.inter ((Set.to_countable U).measurableSet.preimage (measurable_pi_apply a))
  have h := encoded_query_fresh B hB n s a ha U
  change encodedEntropyLaw B F = encodedEntropyLaw B E * readLaw B a U at h
  rw [← entropyCode_law B hB, Measure.map_apply code_meas hF, Measure.map_apply code_meas hE] at h
  have he0 : entropyCode ⁻¹' E = {ω | CountingLLL.ReciprocalTest.run ω n = s} := by
    ext ω; change (CountingLLL.RevealMachine.run revealProgram (entropyCode ω) initial n).1 = s ↔ _
    rw [reciprocal_reveal_simulates]
    rfl
  have he1 : entropyCode ⁻¹' F = {ω | CountingLLL.ReciprocalTest.run ω n = s ∧ entropyCode ω a ∈ U} := by
    ext ω; change ((CountingLLL.RevealMachine.run revealProgram (entropyCode ω) initial n).1 = s ∧ entropyCode ω a ∈ U) ↔ _
    rw [reciprocal_reveal_simulates]
    rfl
  rw [he0,he1] at h
  exact h
