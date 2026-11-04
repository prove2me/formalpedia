-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_f_weighted_random_measure_finite_simple_integral_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T13:47:31.94935+00:00
-- url     : https://prove2.me/submissions/8cc88dee-7311-46a7-ade1-16a55ed0cb6e

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

/-- Random-measure finite simple-integral measurability follows from
actual cell-mass measurability, not from a substituted model. -/
theorem solution
    {Ω α ι : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (M : Ω → Measure α) (S : Finset ι)
    (C : ι → Set α) (hC : ∀ i ∈ S, MeasurableSet (C i))
    (H : ι → Ω → ℝ≥0∞)
    (hH : ∀ i ∈ S, Measurable (H i))
    (hMass : ∀ i ∈ S, Measurable (fun ω => M ω (C i))) :
    Measurable (fun ω =>
      (∫⁻ x, S.sum (fun i => (C i).indicator (fun _ => H i ω) x) ∂M ω)) := by
  have hPath (ω : Ω) :
      (∫⁻ x, S.sum (fun i => (C i).indicator (fun _ => H i ω) x) ∂M ω) =
      S.sum (fun i => H i ω * M ω (C i)) := by
    calc
      (∫⁻ x, S.sum (fun i => (C i).indicator (fun _ => H i ω) x) ∂M ω) =
          S.sum (fun i => (∫⁻ x, (C i).indicator (fun _ => H i ω) x ∂M ω)) := by
            exact lintegral_finset_sum S
              (by
                intro i hi
                exact measurable_const.indicator (hC i hi))
      _ = S.sum (fun i => H i ω * M ω (C i)) := by
            apply Finset.sum_congr rfl
            intro i hi
            simp [lintegral_indicator (hC i hi), mul_comm]
  have hFun :
      (fun ω => (∫⁻ x, S.sum (fun i => (C i).indicator (fun _ => H i ω) x) ∂M ω)) =
      (fun ω => S.sum (fun i => H i ω * M ω (C i))) := by
    funext ω
    exact hPath ω
  rw [hFun]
  exact Finset.measurable_sum S
    (by
      intro i hi
      exact (hH i hi).mul (hMass i hi))
