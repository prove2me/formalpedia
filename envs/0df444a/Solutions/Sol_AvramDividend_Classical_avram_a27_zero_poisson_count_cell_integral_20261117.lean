-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_zero_poisson_count_cell_integral_20261117
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T16:08:42.232337+00:00
-- url     : https://prove2.me/submissions/75e4680f-2549-4711-a1ab-2a2e9ba90ba6

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
noncomputable section

/-- Integrating a unit weight on the zero Poisson count cell gives its law mass. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (r : ℝ≥0) (hLaw : HasLaw K (poissonMeasure r) P)
    (F : Ω → ℝ)
    (hF : ∀ᵐ ω ∂P, K ω = 0 → F ω = 1) :
    (∫ ω in {ω : Ω | K ω = 0}, F ω ∂P) =
      (poissonMeasure r).real {0} := by
  classical
  have hSet : MeasurableSet {ω : Ω | K ω = 0} :=
    hK (measurableSet_singleton 0)
  have hEq :
      ({ω : Ω | K ω = 0}).indicator F =ᵐ[P]
        ({ω : Ω | K ω = 0}).indicator (fun _ => (1 : ℝ)) := by
    filter_upwards [hF] with ω hω
    by_cases hk : K ω = 0
    · simp [Set.indicator_apply, hk, hω hk]
    · simp [Set.indicator_apply, hk]
  have heq : P {ω : Ω | K ω = 0} = poissonMeasure r {0} := by
    rw [show {ω : Ω | K ω = 0} = K ⁻¹' {0} from rfl,
      ← Measure.map_apply hK (measurableSet_singleton 0), hLaw.map_eq]
  calc
    _ = (∫ ω, ({ω : Ω | K ω = 0}).indicator F ω ∂P) := by
      rw [← integral_indicator hSet]
    _ = (∫ ω,
      ({ω : Ω | K ω = 0}).indicator (fun _ => (1 : ℝ)) ω ∂P) :=
        integral_congr_ae hEq
    _ = P.real {ω : Ω | K ω = 0} := by
      rw [integral_indicator_const (1 : ℝ) hSet]
      simp
    _ = (poissonMeasure r).real {0} := by
      rw [measureReal_def, heq, ← measureReal_def]
