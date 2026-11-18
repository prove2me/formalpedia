-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_indep_poisson_count_cell_laplace_20261117
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T15:26:35.845353+00:00
-- url     : https://prove2.me/submissions/c520f178-ed42-4ae8-b833-3fa151e6b8a8

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
noncomputable section
/-- The independent-mark source integral over one Poisson count cell. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (N : Ω → ℕ) (Y : ℕ → Ω → ℝ)
    (hN : Measurable N) (hY : ∀ n, Measurable (Y n))
    (hNY : IndepFun N (fun ω n => Y n ω) P)
    (r : ℝ≥0) (hLaw : HasLaw N (poissonMeasure r) P)
    (θ m : ℝ)
    (hMarks : ∀ k, (∫ ω,
      Real.exp (θ * ∑ j ∈ Finset.range k, Y j ω) ∂P) = m ^ k)
    (k : ℕ) :
    (∫ ω in {ω : Ω | N ω = k},
      Real.exp (θ * ∑ j ∈ Finset.range (N ω), Y j ω) ∂P) =
      (poissonMeasure r).real {k} * m ^ k := by
  classical
  have hs : MeasurableSet {ω : Ω | N ω = k} := hN (measurableSet_singleton k)
  have hcong : Set.EqOn
      (fun ω => Real.exp (θ * ∑ j ∈ Finset.range (N ω), Y j ω))
      (fun ω => Real.exp (θ * ∑ j ∈ Finset.range k, Y j ω))
      {ω : Ω | N ω = k} := by
    intro ω h
    simp only [Set.mem_setOf_eq] at h
    simp [h]
  have hprod :
      (∫ ω, (if N ω = k then (1 : ℝ) else 0) *
        Real.exp (θ * ∑ j ∈ Finset.range k, Y j ω) ∂P) =
      (∫ ω, if N ω = k then (1 : ℝ) else 0 ∂P) *
        ∫ ω, Real.exp (θ * ∑ j ∈ Finset.range k, Y j ω) ∂P :=
    hNY.integral_fun_comp_mul_comp
      (f := fun n : ℕ => if n = k then (1 : ℝ) else 0)
      (g := fun y : ℕ → ℝ => Real.exp (θ * ∑ j ∈ Finset.range k, y j))
      hN.aemeasurable (measurable_pi_lambda _ hY).aemeasurable
      (measurable_of_countable _).aestronglyMeasurable
      (by fun_prop)
  have hμreal : P.real {ω : Ω | N ω = k} = (poissonMeasure r).real {k} := by
    have heq : P {ω : Ω | N ω = k} = poissonMeasure r {k} := by
      rw [show {ω : Ω | N ω = k} = N ⁻¹' {k} from rfl,
        ← Measure.map_apply hN (measurableSet_singleton k), hLaw.map_eq]
    rw [measureReal_def, heq, ← measureReal_def]
  have hfint : (∫ ω, if N ω = k then (1 : ℝ) else 0 ∂P) =
      (poissonMeasure r).real {k} := by
    have heq : (fun ω => if N ω = k then (1 : ℝ) else 0) =
      ({ω : Ω | N ω = k}).indicator fun _ => (1 : ℝ) := by
      funext ω
      simp only [Set.indicator_apply, Set.mem_setOf_eq]
    rw [heq, integral_indicator_const (1 : ℝ) hs, hμreal]
    simp
  calc
    _ = (∫ ω in {ω : Ω | N ω = k},
        Real.exp (θ * ∑ j ∈ Finset.range k, Y j ω) ∂P) :=
          setIntegral_congr_fun hs hcong
    _ = (∫ ω, (if N ω = k then (1 : ℝ) else 0) *
        Real.exp (θ * ∑ j ∈ Finset.range k, Y j ω) ∂P) := by
          rw [← integral_indicator hs]
          congr 1
          funext ω
          simp only [Set.indicator_apply, Set.mem_setOf_eq]
          by_cases h : N ω = k <;> simp [h]
    _ = _ := by rw [hprod, hfint, hMarks]
