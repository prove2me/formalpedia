-- Prove2me | solution 1 for CountingLLL.ReciprocalTest.suppressed_history_fresh
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:59:47.831842+00:00
-- url     : https://prove2.me/submissions/31104e38-fa46-461e-ab49-fe657088e67e

import Definitions.Def_CountingLLL_ReciprocalEncodedLaw
import Theorems.Thm_CountingLLL_ReciprocalTest_entropyCode_law
import Theorems.Thm_CountingLLL_ReciprocalTest_encoded_read_marginals
import Theorems.Thm_CountingLLL_ReciprocalTest_suppressed_reveal_fresh_simulation
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

theorem solution (B : ℝ≥0∞) (hB : B ≤ 1) (n : ℕ) (s : State) (a : ReadIndex)
    (ha : readIndex s = some a) (H : (Fin (n+1) → State) → Prop) (U : Set ℕ) :
    entropyLaw B {ω | H (fun j => allSuppressedRun ω j.val) ∧
      allSuppressedRun ω n = s ∧ entropyCode ω a ∈ U} =
    entropyLaw B {ω | H (fun j => allSuppressedRun ω j.val) ∧
      allSuppressedRun ω n = s} * readLaw B a U := by
  classical
  letI (i : ReadIndex) : IsProbabilityMeasure (readLaw B i) := (encoded_read_marginals B hB).1 i
  let H' : (Fin (n+1) → State) → Prop := fun f => H f ∧ f ⟨n, by omega⟩ = s
  let E : Set (ReadIndex → ℕ) := {x | H' (fun j => (CountingLLL.RevealMachine.run suppressedRevealProgram x initial j.val).1)}
  let F : Set (ReadIndex → ℕ) := E ∩ {x | x a ∈ U}
  have hE : MeasurableSet E := history_event_meas n H'
  have hF : MeasurableSet F := hE.inter ((Set.to_countable U).measurableSet.preimage (measurable_pi_apply a))
  have h := history_fresh_query suppressedRevealProgram initial n a H' (readLaw B) U (Set.to_countable U).measurableSet
    (by intro x hx hq; exact (suppressed_reveal_fresh_simulation.2 x n a hq))
  have hEeq : {x | H' (fun j => (CountingLLL.RevealMachine.run suppressedRevealProgram x initial j.val).1) ∧
      suppressedRevealProgram.query (CountingLLL.RevealMachine.run suppressedRevealProgram x initial n).1 = some a} = E := by
    ext x
    simp only [E, H', Set.mem_setOf_eq]
    constructor
    · intro hx; exact hx.1
    · rintro ⟨hh, hs⟩
      refine ⟨⟨hh,hs⟩, ?_⟩
      change readIndex (CountingLLL.RevealMachine.run suppressedRevealProgram x initial n).1 = some a
      rw [hs,ha]
  have hFeq : {x | H' (fun j => (CountingLLL.RevealMachine.run suppressedRevealProgram x initial j.val).1) ∧
      suppressedRevealProgram.query (CountingLLL.RevealMachine.run suppressedRevealProgram x initial n).1 = some a ∧ x a ∈ U} = F := by
    ext x
    have hh := Set.ext_iff.mp hEeq x
    simp only [Set.mem_setOf_eq, E, H'] at hh
    simp only [F, E, Set.mem_inter_iff, Set.mem_setOf_eq, H']
    exact ⟨fun ⟨hhist,hq,hv⟩ => ⟨hhist,hv⟩, fun ⟨hhist,hv⟩ => ⟨hhist,(hh.mpr hhist).2,hv⟩⟩
  have h' : encodedEntropyLaw B F = encodedEntropyLaw B E * readLaw B a U := by
    change (Measure.infinitePi (readLaw B)) F = (Measure.infinitePi (readLaw B)) E * readLaw B a U
    rw [hFeq, hEeq] at h
    exact h
  rw [← entropyCode_law B hB, Measure.map_apply code_meas hF, Measure.map_apply code_meas hE] at h'
  have he0 : entropyCode ⁻¹' E = {ω | H (fun j => allSuppressedRun ω j.val) ∧ allSuppressedRun ω n = s} := by
    ext ω
    simp only [Set.mem_preimage, E, Set.mem_setOf_eq, H']
    simp only [suppressed_reveal_fresh_simulation.1]
  have he1 : entropyCode ⁻¹' F = {ω | H (fun j => allSuppressedRun ω j.val) ∧ allSuppressedRun ω n = s ∧ entropyCode ω a ∈ U} := by
    ext ω
    simp only [Set.mem_preimage, F, E, Set.mem_inter_iff, Set.mem_setOf_eq, H']
    simp only [suppressed_reveal_fresh_simulation.1, and_assoc]
  rw [he0,he1] at h'
  exact h'
