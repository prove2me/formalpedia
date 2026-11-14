-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a206_original_discount_first_energy_width_square_rate_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:07:32.719769+00:00
-- url     : https://prove2.me/submissions/86e397bc-4c8b-48af-9af5-2ddafa28f6c1

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ga_a82_original_gaussian_mesh_drift_square_mass_tendsto_of_width
import Theorems.Thm_AvramDividend_Classical_avram_ga_a83_original_gaussian_uniform_mesh_time_mass_le_horizon
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_uniform_time_mesh_width_tendsto_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal
noncomputable section

/-- Deterministic rate of the original Gaussian first-source discount mesh
energy majorant tends to zero through the proved bounded mesh time mass. -/
theorem solution
    (n : ℕ) (q L K : ℝ) :
    Tendsto (fun m : ℕ =>
      (q * (((n : ℝ≥0) / ((m : ℝ≥0) + 1) : ℝ≥0) : ℝ) * L)^2 *
        ((m : ℝ) * K)) atTop (𝓝 (0 : ℝ)) := by
  let Δ : ℕ → ℝ≥0 := fun m =>
    (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  have hΔnn : Tendsto Δ atTop (𝓝 (0 : ℝ≥0)) := by
    simpa only [Δ] using
      avram_p2_34dbea70_uniform_time_mesh_width_tendsto_zero
        (n : ℝ≥0)
  have hΔ : Tendsto (fun m : ℕ => (Δ m : ℝ))
      atTop (𝓝 (0 : ℝ)) := by
    change Tendsto (NNReal.toReal ∘ Δ) atTop (𝓝 (↑(0 : ℝ≥0) : ℝ))
    exact (NNReal.continuous_coe.tendsto 0).comp hΔnn
  have hMass (m : ℕ) : (m : ℝ) * (Δ m : ℝ) ≤ (n : ℝ) := by
    simpa only [Δ] using
      avram_ga_a83_original_gaussian_uniform_mesh_time_mass_le_horizon n m
  have hRate :=
    avram_ga_a82_original_gaussian_mesh_drift_square_mass_tendsto_of_width
      n Δ hΔ hMass (q * L)
  have hScaled := hRate.mul_const K
  convert hScaled using 1
  · funext m
    dsimp [Δ]
    ring
  · ring
