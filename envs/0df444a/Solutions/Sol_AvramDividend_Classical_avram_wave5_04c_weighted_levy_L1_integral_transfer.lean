-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_weighted_levy_L1_integral_transfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T18:31:48.500148+00:00
-- url     : https://prove2.me/submissions/27c9f0a0-e887-44fc-a57b-86968bff9d83

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory

/-! Dominated signed Bochner integrals inherit the exact weighted error. -/
theorem solution {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (F G H : α → ℝ)
    (hF : Integrable F μ) (hG : Integrable G μ)
    (hH : Integrable H μ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hbd : ∀ᵐ z ∂μ, |F z - G z| ≤ ε * H z) :
    |(∫ z, F z ∂μ) - (∫ z, G z ∂μ)| ≤
      ε * (∫ z, H z ∂μ) := by
  have hdiff : Integrable (fun z => F z - G z) μ := hF.sub hG
  have hnorm : Integrable (fun z => |F z - G z|) μ := hdiff.abs
  have hweighted : Integrable (fun z => ε * H z) μ :=
    hH.const_mul ε
  rw [← integral_sub hF hG]
  calc
    |∫ z, F z - G z ∂μ| ≤
        ∫ z, |F z - G z| ∂μ :=
      abs_integral_le_integral_abs
    _ ≤ ∫ z, ε * H z ∂μ :=
      integral_mono_ae hnorm hweighted hbd
    _ = ε * (∫ z, H z ∂μ) := integral_const_mul _ _
