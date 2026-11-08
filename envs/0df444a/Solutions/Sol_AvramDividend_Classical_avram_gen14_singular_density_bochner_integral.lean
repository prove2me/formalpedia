-- Prove2me | solution 1 for AvramDividend.Classical.avram_gen14_singular_density_bochner_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T13:34:22.631207+00:00
-- url     : https://prove2.me/submissions/35f5040d-ca1c-40a2-8472-97220ce2e71e

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gen14_singular_levy_density_measurable_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set
open scoped ENNReal
noncomputable section

/-- Convert the proposed singular Levy density integral into weighted volume. -/
theorem solution (g : ℝ → ℝ) :
    (∫ z, g z ∂(volume.withDensity (fun z : ℝ =>
      if z ∈ Ioo (-1 : ℝ) 0
      then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0))) =
    (∫ z, (if z ∈ Ioo (-1 : ℝ) 0
      then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0).toReal * g z ∂volume) := by
  obtain ⟨hmeas, hfinite⟩ :=
    AvramDividend.Classical.avram_gen14_singular_levy_density_measurable_finite
  have hae : ∀ᵐ z ∂(volume : Measure ℝ),
      (if z ∈ Ioo (-1 : ℝ) 0
        then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0) < ⊤ :=
    Filter.Eventually.of_forall hfinite
  simpa only [smul_eq_mul] using
    (integral_withDensity_eq_integral_toReal_smul hmeas hae g)
