-- Prove2me | solution 1 for CountingLLL.ReciprocalTest.encoded_query_fresh
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:00:52.753356+00:00
-- url     : https://prove2.me/submissions/e5d26234-2fa0-4c00-9627-e26aafb0ef03

import Definitions.Def_CountingLLL_ReciprocalEncodedLaw
import Theorems.Thm_CountingLLL_RevealMachine_fresh_query_probability
import Theorems.Thm_CountingLLL_ReciprocalTest_reciprocal_query_fresh

set_option autoImplicit false
open MeasureTheory ProbabilityTheory CountingLLL.ReciprocalTest CountingLLL.RevealMachine
open scoped ENNReal

private theorem oracle_probability (B : ℝ≥0∞) (hB : B ≤ 1) : IsProbabilityMeasure (oracleLaw B) := by
  constructor
  simp only [oracleLaw, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [add_comm, tsub_add_cancel_of_le hB]

private theorem fair_probability : IsProbabilityMeasure fairLaw := by
  constructor
  simp only [fairLaw, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← two_mul, one_div, ENNReal.mul_inv_cancel (by norm_num) (by simp)]

private theorem uniform_probability (n : ℕ) : IsProbabilityMeasure (uniformLaw n) := by
  constructor
  simp [uniformLaw, Measure.smul_apply, Measure.count_apply, ENNReal.inv_mul_cancel]

private theorem readLaw_probability (B : ℝ≥0∞) (hB : B ≤ 1) (a : ReadIndex) :
    IsProbabilityMeasure (readLaw B a) := by
  letI := oracle_probability B hB
  letI := fair_probability
  cases a with
  | inl i => exact Measure.isProbabilityMeasure_map (by fun_prop : Measurable bitCode).aemeasurable
  | inr x =>
    cases x with
    | inl i => exact Measure.isProbabilityMeasure_map (by fun_prop : Measurable bitCode).aemeasurable
    | inr a =>
      letI := uniform_probability a.1
      exact Measure.isProbabilityMeasure_map (by fun_prop : Measurable (fun x : Fin (a.1+1) => x.val)).aemeasurable

/-- Every encoded query retains its coordinate marginal conditional on the current state. -/
theorem solution (B : ℝ≥0∞) (hB : B ≤ 1) (n : ℕ) (s : State) (a : ReadIndex)
    (ha : readIndex s = some a) (U : Set ℕ) :
    encodedEntropyLaw B {x | (CountingLLL.RevealMachine.run revealProgram x initial n).1 = s ∧ x a ∈ U} =
      encodedEntropyLaw B {x | (CountingLLL.RevealMachine.run revealProgram x initial n).1 = s} * readLaw B a U := by
  letI (i : ReadIndex) : IsProbabilityMeasure (readLaw B i) := readLaw_probability B hB i
  let R : Set State := {s}
  let A : ReadIndex → Set ℕ := fun _ => U
  have hA : ∀ i, MeasurableSet (A i) := by intro i; exact (Set.to_countable _).measurableSet
  have h := fresh_query_probability revealProgram initial n (.inl 0) R (readLaw B) A hA (readLaw B a U)
    (by
      intro x hx hsome
      have hx' : (CountingLLL.RevealMachine.run revealProgram x initial n).1 = s := by simpa [R] using hx
      have hq : readIndex (CountingLLL.RevealMachine.run revealProgram x initial n).1 = some a := by rw [hx']; exact ha
      change (readIndex (CountingLLL.RevealMachine.run revealProgram x initial n).1).getD (.inl 0) ∉ _
      rw [hq]
      exact reciprocal_query_fresh x n _ hq)
    (by
      intro x hx hsome
      have hx' : (CountingLLL.RevealMachine.run revealProgram x initial n).1 = s := by simpa [R] using hx
      change readLaw B ((readIndex (CountingLLL.RevealMachine.run revealProgram x initial n).1).getD (.inl 0)) U = readLaw B a U
      rw [hx', ha]
      rfl)
  have he : {x | (CountingLLL.RevealMachine.run revealProgram x initial n).1 ∈ R ∧
        (revealProgram.query (CountingLLL.RevealMachine.run revealProgram x initial n).1).isSome} =
      {x | (CountingLLL.RevealMachine.run revealProgram x initial n).1 = s} := by
    ext x
    simp only [Set.mem_setOf_eq, R, Set.mem_singleton_iff]
    constructor
    · intro h; exact h.1
    · intro h; refine ⟨h, ?_⟩; change (readIndex (CountingLLL.RevealMachine.run revealProgram x initial n).1).isSome; rw [h,ha]; rfl
  have hsuc : {x | (CountingLLL.RevealMachine.run revealProgram x initial n).1 ∈ R ∧
        (revealProgram.query (CountingLLL.RevealMachine.run revealProgram x initial n).1).isSome ∧
        x ((revealProgram.query (CountingLLL.RevealMachine.run revealProgram x initial n).1).getD (.inl 0)) ∈ A ((revealProgram.query (CountingLLL.RevealMachine.run revealProgram x initial n).1).getD (.inl 0))} =
      {x | (CountingLLL.RevealMachine.run revealProgram x initial n).1 = s ∧ x a ∈ U} := by
    ext x
    simp only [Set.mem_setOf_eq, R, Set.mem_singleton_iff, A]
    constructor
    · rintro ⟨heq, hsome, hval⟩
      refine ⟨heq, ?_⟩
      change x ((readIndex (CountingLLL.RevealMachine.run revealProgram x initial n).1).getD (.inl 0)) ∈ U at hval
      rw [heq, ha] at hval
      exact hval
    · rintro ⟨heq, hval⟩
      refine ⟨heq, ?_, ?_⟩
      · change (readIndex (CountingLLL.RevealMachine.run revealProgram x initial n).1).isSome
        rw [heq,ha]; rfl
      · change x ((readIndex (CountingLLL.RevealMachine.run revealProgram x initial n).1).getD (.inl 0)) ∈ U
        rw [heq,ha]; exact hval
  rw [he, hsuc] at h
  exact h
