-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_generic_nat_family_independent_of_atomic_product
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T11:22:15.082724+00:00
-- url     : https://prove2.me/submissions/394c079c-c275-4b9b-958d-6c3b20943d20

import Mathlib.Probability.Independence.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Finset
noncomputable section

/-- On a finite discrete product, agreement on singleton cylinders forces independence. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (Z : Fin n → Ω → ℕ)
    (hZ : ∀ i, Measurable (Z i))
    (hAtoms : ∀ v : Fin n → ℕ,
      P {ω | ∀ i, Z i ω = v i} =
        ∏ i : Fin n, P {ω | Z i ω = v i}) :
    iIndepFun Z P := by
  classical
  have hPi : Measurable (fun ω => fun i : Fin n => Z i ω) :=
    measurable_pi_iff.mpr hZ
  apply (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
    (fun i => (hZ i).aemeasurable)).2
  apply Measure.ext_of_singleton
  intro v
  have hv : (fun ω => (fun i : Fin n => Z i ω)) ⁻¹' {v} =
      {ω | ∀ i, Z i ω = v i} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq, funext_iff]
  rw [Measure.map_apply hPi (measurableSet_singleton v)]
  rw [Measure.pi_singleton]
  rw [hv, hAtoms v]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Measure.map_apply (hZ i) (measurableSet_singleton (v i))]
  rfl
