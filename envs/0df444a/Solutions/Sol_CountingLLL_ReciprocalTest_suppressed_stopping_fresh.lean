-- Prove2me | solution 1 for CountingLLL.ReciprocalTest.suppressed_stopping_fresh
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T11:10:21.121736+00:00
-- url     : https://prove2.me/submissions/3e86fa5c-a78c-4ca0-9aa1-39fbafd4a5a8

import Definitions.Def_CountingLLL_ReciprocalEncodedLaw
import Theorems.Thm_CountingLLL_ReciprocalTest_entropyCode_law
import Theorems.Thm_CountingLLL_ReciprocalTest_encoded_read_marginals
import Theorems.Thm_CountingLLL_ReciprocalTest_suppressed_reveal_fresh_simulation
import Theorems.Thm_CountingLLL_ReciprocalTest_suppressed_history_fresh
import Theorems.Thm_CountingLLL_RevealMachine_history_fresh_query
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
    MeasurableSet {x : ReadIndex → ℕ | (CountingLLL.RevealMachine.run suppressedRevealProgram x initial n).1 = s} := by
  let C : Finset ReadIndex → Set (ReadIndex → ℕ) := fun S =>
    {x | (CountingLLL.RevealMachine.run suppressedRevealProgram x initial n).1 = s ∧
      (CountingLLL.RevealMachine.run suppressedRevealProgram x initial n).2 = S}
  have hc (S : Finset ReadIndex) : MeasurableSet (C S) := by
    apply finite_dep_meas S (C S)
    intro x y h
    constructor
    · rintro ⟨hstate,hseen⟩
      have heq := run_depends_on_seen suppressedRevealProgram x y initial n (by simpa [hseen] using h)
      exact ⟨by simpa [← heq] using hstate, by simpa [← heq] using hseen⟩
    · rintro ⟨hstate,hseen⟩
      have heq := run_depends_on_seen suppressedRevealProgram y x initial n (by
        intro i hi; exact (h i (by simpa [hseen] using hi)).symm)
      exact ⟨by simpa [← heq] using hstate, by simpa [← heq] using hseen⟩
  have heq : {x : ReadIndex → ℕ | (CountingLLL.RevealMachine.run suppressedRevealProgram x initial n).1 = s} = ⋃ S, C S := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro hs; exact ⟨(CountingLLL.RevealMachine.run suppressedRevealProgram x initial n).2, hs, rfl⟩
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


private theorem history_event_meas (n : ℕ) (H : (Fin (n+1) → State) → Prop) :
    MeasurableSet {x : ReadIndex → ℕ | H (fun j => (CountingLLL.RevealMachine.run suppressedRevealProgram x initial j.val).1)} := by
  classical
  let C : (Fin (n+1) → State) → Set (ReadIndex → ℕ) := fun f =>
    if H f then ⋂ j : Fin (n+1), {x | (CountingLLL.RevealMachine.run suppressedRevealProgram x initial j.val).1 = f j} else ∅
  have hc (f : Fin (n+1) → State) : MeasurableSet (C f) := by
    by_cases hf : H f
    · simp only [C, if_pos hf]
      exact MeasurableSet.iInter (fun j => state_event_meas j.val (f j))
    · simp [C, hf]
  have heq : {x : ReadIndex → ℕ | H (fun j => (CountingLLL.RevealMachine.run suppressedRevealProgram x initial j.val).1)} = ⋃ f, C f := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, C]
    constructor
    · intro hx
      refine ⟨(fun j => (CountingLLL.RevealMachine.run suppressedRevealProgram x initial j.val).1), ?_⟩
      simp [hx]
    · rintro ⟨f, hf⟩
      by_cases hH : H f
      · simp only [if_pos hH, Set.mem_iInter, Set.mem_setOf_eq] at hf
        have : (fun j : Fin (n+1) => (CountingLLL.RevealMachine.run suppressedRevealProgram x initial j.val).1) = f := funext hf
        simpa [this] using hH
      · simp [hH] at hf
  rw [heq]
  exact MeasurableSet.iUnion hc


private theorem operational_history_meas (n : ℕ) (H : (Fin (n+1) → State) → Prop) :
    MeasurableSet {ω : Entropy | H (fun j => allSuppressedRun ω j.val)} := by
  have h := (history_event_meas n H).preimage code_meas
  have he : entropyCode ⁻¹' {x | H (fun j => (CountingLLL.RevealMachine.run suppressedRevealProgram x initial j.val).1)} =
      {ω | H (fun j => allSuppressedRun ω j.val)} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_setOf_eq, suppressed_reveal_fresh_simulation.1]
  simpa only [he] using h

/-- Fresh-coordinate law at any almost surely finite or infinite history stopping rule. -/
theorem solution (B : ℝ≥0∞) (hB : B ≤ 1) (T : Entropy → Option ℕ)
    (H : (n : ℕ) → (Fin (n+1) → State) → Prop)
    (hT : ∀ ω n, T ω = some n ↔ H n (fun j => allSuppressedRun ω j.val))
    (s : State) (a : ReadIndex) (ha : readIndex s = some a) (U : Set ℕ) :
    entropyLaw B {ω | ∃ n, T ω = some n ∧ allSuppressedRun ω n = s ∧ entropyCode ω a ∈ U} =
      entropyLaw B {ω | ∃ n, T ω = some n ∧ allSuppressedRun ω n = s} * readLaw B a U := by
  classical
  let E : ℕ → Set Entropy := fun n => {ω | T ω = some n ∧ allSuppressedRun ω n = s}
  let F : ℕ → Set Entropy := fun n => {ω | T ω = some n ∧ allSuppressedRun ω n = s ∧ entropyCode ω a ∈ U}
  have hE (n : ℕ) : MeasurableSet (E n) := by
    have h := operational_history_meas n (fun f => H n f ∧ f ⟨n, by omega⟩ = s)
    convert h using 1
    ext ω
    simp only [E, Set.mem_setOf_eq]
    exact and_congr (hT ω n) Iff.rfl
  have hF (n : ℕ) : MeasurableSet (F n) := by
    have he : F n = E n ∩ (entropyCode ⁻¹' {x | x a ∈ U}) := by ext ω; simp [E,F,and_assoc]
    rw [he]
    exact (hE n).inter (((Set.to_countable U).measurableSet.preimage (measurable_pi_apply a)).preimage code_meas)
  have hdisjE : Pairwise (fun i j => Disjoint (E i) (E j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro ω hi hj
    exact hij (Option.some.inj (hi.1.symm.trans hj.1))
  have hdisjF : Pairwise (fun i j => Disjoint (F i) (F j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro ω hi hj
    exact hij (Option.some.inj (hi.1.symm.trans hj.1))
  have hfac (n : ℕ) : entropyLaw B (F n) = entropyLaw B (E n) * readLaw B a U := by
    have h := suppressed_history_fresh B hB n s a ha (H n) U
    have e0 : E n = {ω | H n (fun j => allSuppressedRun ω j.val) ∧ allSuppressedRun ω n = s} := by
      ext ω; simp [E,hT ω n]
    have f0 : F n = {ω | H n (fun j => allSuppressedRun ω j.val) ∧ allSuppressedRun ω n = s ∧ entropyCode ω a ∈ U} := by
      ext ω; simp [F,hT ω n]
    rw [e0,f0]
    exact h
  have he : {ω | ∃ n, T ω = some n ∧ allSuppressedRun ω n = s} = ⋃ n, E n := by
    ext ω; simp [E]
  have hf : {ω | ∃ n, T ω = some n ∧ allSuppressedRun ω n = s ∧ entropyCode ω a ∈ U} = ⋃ n, F n := by
    ext ω; simp [F]
  rw [hf,he,measure_iUnion hdisjF hF, measure_iUnion hdisjE hE]
  simp_rw [hfac]
  exact ENNReal.tsum_mul_right
