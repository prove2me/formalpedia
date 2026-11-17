-- Prove2me | solution 1 for AvramDividend.Classical.avram_a28_probability_full_finite_rectangle_factorisation_implies_iIndepFun_20261116
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T12:37:45.652198+00:00
-- url     : https://prove2.me/submissions/b4401397-5cfe-49cd-89bf-888bfde6ca98

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
noncomputable section
theorem solution
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (n : ℕ) (Y : ℕ → Ω → E)
    (hFull : ∀ (A : Fin n → Set E),
      (∀ i, MeasurableSet (A i)) →
      P {ω : Ω | ∀ i : Fin n, Y i.val ω ∈ A i} =
        ∏ i : Fin n, P (Y i.val ⁻¹' A i)) :
    iIndepFun (fun i : Fin n => Y i.val) P := by
  classical
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hm
  let A : Fin n → Set E := fun i => if i ∈ S then sets i else Set.univ
  have hA : ∀ i, MeasurableSet (A i) := by
    intro i
    by_cases hi : i ∈ S
    · simpa [A, hi] using hm i hi
    · simp [A, hi]
  have h := hFull A hA
  have hL : {ω : Ω | ∀ i : Fin n, Y i.val ω ∈ A i} =
      (⋂ i ∈ S, Y i.val ⁻¹' sets i) := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
    constructor
    · intro hh i hi
      simpa [A, hi] using hh i
    · intro hh i
      by_cases hi : i ∈ S
      · simpa [A, hi] using hh i hi
      · simp [A, hi]
  have hR : (∏ i : Fin n, P (Y i.val ⁻¹' A i)) =
      (∏ i ∈ S, P (Y i.val ⁻¹' sets i)) := by
    have hTerm : ∀ i : Fin n,
        P (Y i.val ⁻¹' A i) =
          if i ∈ S then P (Y i.val ⁻¹' sets i) else 1 := by
      intro i
      by_cases hi : i ∈ S
      · simp [A, hi]
      · simp [A, hi, measure_univ]
    simp_rw [hTerm]
    simp [Finset.prod_ite_mem]
  simpa only [hL, hR] using h
