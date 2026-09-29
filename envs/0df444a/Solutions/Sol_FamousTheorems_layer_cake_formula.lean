-- Prove2me | solution 1 for FamousTheorems.layer_cake_formula
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:06:44.850297+00:00
-- url     : https://prove2.me/submissions/bb6f6072-8669-4d7d-9dd2-86211e17905f

import Mathlib

open MeasureTheory

theorem solution {α : Type*} [MeasurableSpace α] (μ : Measure α) {f : α → ℝ} {g : ℝ → ℝ} (f_nn : 0 ≤ᵐ[μ] f)
    (f_mble : AEMeasurable f μ) (g_intble : ∀ t > 0, IntervalIntegrable g volume 0 t)
    (g_nn : ∀ᵐ t ∂(volume.restrict (Set.Ioi 0)), 0 ≤ g t) :
    ∫⁻ ω, ENNReal.ofReal (∫ t in (0 : ℝ)..f ω, g t) ∂μ =
      ∫⁻ t in Set.Ioi 0, μ {a | t ≤ f a} * ENNReal.ofReal (g t) :=
  MeasureTheory.lintegral_comp_eq_lintegral_meas_le_mul μ f_nn f_mble g_intble g_nn
