-- Prove2me | solution 1 for CountingLLL.ReciprocalTest.encoded_read_marginals
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:59:14.11821+00:00
-- url     : https://prove2.me/submissions/0955803b-e175-4a7d-9ebc-47c8457ccd6f

import Definitions.Def_CountingLLL_ReciprocalEncodedLaw
set_option autoImplicit false
open MeasureTheory ProbabilityTheory CountingLLL.ReciprocalTest
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

private theorem oracle_zero_mass (B : ℝ≥0∞) (i : ℕ) : readLaw B (.inl i) {0} = B := by
  simp [readLaw, Measure.map_apply (by fun_prop : Measurable bitCode), bitCode, oracleLaw, Measure.add_apply, Measure.smul_apply]

private theorem fair_one_mass (B : ℝ≥0∞) (i : ℕ) : readLaw B (.inr (.inl i)) {1} = 1/2 := by
  simp [readLaw, Measure.map_apply (by fun_prop : Measurable bitCode), bitCode, fairLaw, Measure.add_apply, Measure.smul_apply]

private theorem uniform_zero_mass (B : ℝ≥0∞) (a : ℕ × ℕ) :
    readLaw B (.inr (.inr a)) {0} = 1/((a.1+1 : ℕ) : ℝ≥0∞) := by
  rw [readLaw, Measure.map_apply (by fun_prop : Measurable (fun x : Fin (a.1+1) => x.val)) (MeasurableSet.singleton 0)]
  have he : (fun x : Fin (a.1+1) => x.val) ⁻¹' ({0} : Set ℕ) = ({0} : Set (Fin (a.1+1))) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h; exact Fin.ext h
    · intro h; exact congrArg Fin.val h
  rw [he]
  simp [uniformLaw, Measure.smul_apply, Measure.count_singleton]

/-- Normalization and the three relevant encoded read probabilities. -/
theorem solution (B : ℝ≥0∞) (hB : B ≤ 1) :
    (∀ a, IsProbabilityMeasure (readLaw B a)) ∧
    (∀ i, readLaw B (.inl i) {0} = B) ∧
    (∀ i, readLaw B (.inr (.inl i)) {1} = 1/2) ∧
    (∀ a, readLaw B (.inr (.inr a)) {0} = 1/((a.1+1 : ℕ) : ℝ≥0∞)) := by
  exact ⟨readLaw_probability B hB, oracle_zero_mass B, fair_one_mass B, uniform_zero_mass B⟩
