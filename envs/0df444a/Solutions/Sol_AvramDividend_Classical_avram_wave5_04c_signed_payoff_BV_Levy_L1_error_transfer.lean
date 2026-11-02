-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_signed_payoff_BV_Levy_L1_error_transfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:44:35.758687+00:00
-- url     : https://prove2.me/submissions/9a722f01-be53-4c94-a348-ac87fc65ea67

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory

/-! A signed-payoff tail, rather than a global jump first moment, is the
correct dominated-convergence majorant for the genuine BV Levy measure. -/
theorem solution {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (F G H T : α → ℝ)
    (hF : Integrable F μ) (hG : Integrable G μ)
    (hH : Integrable H μ) (hT : Integrable T μ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hbd : ∀ᵐ z ∂μ, |F z - G z| ≤ ε * H z + 2 * T z) :
    |(∫ z, F z ∂μ) - (∫ z, G z ∂μ)| ≤
      ε * (∫ z, H z ∂μ) + 2 * (∫ z, T z ∂μ) := by
  have hdiff : Integrable (fun z => F z - G z) μ := hF.sub hG
  have hweighted : Integrable (fun z => ε * H z + 2 * T z) μ :=
    (hH.const_mul ε).add (hT.const_mul 2)
  rw [← integral_sub hF hG]
  calc
    |∫ z, F z - G z ∂μ| ≤
        ∫ z, |F z - G z| ∂μ :=
      abs_integral_le_integral_abs
    _ ≤ ∫ z, ε * H z + 2 * T z ∂μ :=
      integral_mono_ae hdiff.abs hweighted hbd
    _ = ε * (∫ z, H z ∂μ) + 2 * (∫ z, T z ∂μ) := by
      rw [integral_add (hH.const_mul ε) (hT.const_mul 2)]
      simp only [integral_const_mul]
