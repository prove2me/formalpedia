-- Prove2me | solution 1 for AvramDividend.Classical.finite_measure_cumulative_atom_integral_of_restrict_density
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T11:14:45.971831+00:00
-- url     : https://prove2.me/submissions/a8b5b0c4-3ca5-40fd-a6bf-b9e990cba32f

import Theorems.Thm_AvramDividend_Classical_finite_measure_cumulative_atom_integral_of_density
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped ENNReal

/-- A positive-side density for a finite measure determines its cumulative primitive. -/
theorem solution
    (β : Measure ℝ) (hβfin : β Set.univ ≠ ⊤)
    (f : ℝ → ℝ) (hfnn : ∀ y : ℝ, 0 ≤ f y)
    (hβdensity :
      β.restrict (Ioi (0 : ℝ)) =
        (volume.withDensity (fun y : ℝ => ENNReal.ofReal (f y))).restrict
          (Ioi (0 : ℝ)))
    (hfi : ∀ x : ℝ, 0 < x → IntervalIntegrable f volume 0 x) :
    ∀ x : ℝ, 0 < x →
      (β (Iic x)).toReal =
        (β (Iic (0 : ℝ))).toReal + ∫ y in (0 : ℝ)..x, f y := by
  have hIoc : ∀ x : ℝ, 0 ≤ x →
      β (Ioc (0 : ℝ) x) =
        (volume.withDensity (fun y : ℝ => ENNReal.ofReal (f y)))
          (Ioc (0 : ℝ) x) := by
    intro x hx
    have hsubset : Ioc (0 : ℝ) x ⊆ Ioi (0 : ℝ) := by
      intro y hy
      exact hy.1
    have heq := congrArg
      (fun μ : Measure ℝ => μ (Ioc (0 : ℝ) x)) hβdensity
    simpa [Measure.restrict_apply, Set.inter_eq_self_of_subset_left hsubset] using heq
  exact finite_measure_cumulative_atom_integral_of_density
    β hβfin f hfnn hIoc hfi