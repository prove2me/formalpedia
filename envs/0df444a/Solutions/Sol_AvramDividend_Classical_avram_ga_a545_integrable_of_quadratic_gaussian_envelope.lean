-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a545_integrable_of_quadratic_gaussian_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:48:51.110095+00:00
-- url     : https://prove2.me/submissions/61558c8c-cc8e-4bf0-9470-8a204742616b

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] (f z : Ω → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hf : AEStronglyMeasurable f P)
    (hzsq : Integrable (fun ω => (z ω)^2) P)
    (hBound : ∀ᵐ ω ∂P, |f ω| ≤ M * (1 + (z ω)^2)) :
    Integrable f P := by
  have hdom : Integrable
      (fun ω => M * (1 + (z ω)^2)) P :=
    ((integrable_const 1).add hzsq).const_mul M
  exact hdom.mono' hf (by
    filter_upwards [hBound] with ω hω
    simpa [Real.norm_eq_abs] using hω)
