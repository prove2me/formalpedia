-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a86_original_gaussian_uniform_mesh_drift_square_mass_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T08:06:30.086126+00:00
-- url     : https://prove2.me/submissions/e5537592-aa3c-472f-abea-76a1ce330268

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a82_original_gaussian_mesh_drift_square_mass_tendsto_of_width
import Theorems.Thm_AvramDividend_Classical_avram_ga_a83_original_gaussian_uniform_mesh_time_mass_le_horizon
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_uniform_nnreal_width_tendsto_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology AvramDividend.Classical
open scoped NNReal

/-- The actual original Gaussian physical uniform-grid total squared drift correction tends to zero, with no extra mesh assumptions. -/
theorem solution (n : ℕ) (c : ℝ) :
    Tendsto (fun m : ℕ =>
      (m : ℝ) *
        (((((n : ℝ≥0) / ((m : ℝ≥0) + 1) : ℝ≥0) : ℝ) * c)^2))
        atTop (𝓝 (0 : ℝ)) := by
  let Δ : ℕ → ℝ≥0 := fun m =>
    (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  have hΔnn : Tendsto Δ atTop (𝓝 (0 : ℝ≥0)) := by
    simpa only [Δ] using
      (avram_p2_a_zero_rate_uniform_nnreal_width_tendsto_zero n)
  have hΔ : Tendsto (fun m : ℕ => (Δ m : ℝ))
      atTop (𝓝 (0 : ℝ)) := NNReal.tendsto_coe.mpr hΔnn
  have hMass (m : ℕ) : (m : ℝ) * (Δ m : ℝ) ≤ (n : ℝ) := by
    simpa only [Δ] using
      (avram_ga_a83_original_gaussian_uniform_mesh_time_mass_le_horizon n m)
  simpa only [Δ] using
    (avram_ga_a82_original_gaussian_mesh_drift_square_mass_tendsto_of_width
      n Δ hΔ hMass c)
