-- Prove2me | solution 1 for AvramDividend.Classical.avram_gen14_singular_levy_first_moment_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T13:54:44.952359+00:00
-- url     : https://prove2.me/submissions/43159f08-4684-4069-85cf-b572f0bd0415

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gen14_singular_levy_absolute_first_moment
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal
noncomputable section

/-- The nonzero first-moment value forces Bochner integrability. -/
theorem solution :
    Integrable (fun z : ℝ => |z|)
      (volume.withDensity (fun z : ℝ =>
        if z ∈ Ioo (-1 : ℝ) 0
        then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0)) := by
  by_contra h
  have hzero :
      (∫ z : ℝ, |z| ∂(volume.withDensity (fun z : ℝ =>
        if z ∈ Ioo (-1 : ℝ) 0
        then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0))) = 0 :=
    integral_undef h
  have htwo := avram_gen14_singular_levy_absolute_first_moment
  linarith
