-- Prove2me | solution 1 for AvramDividend.Classical.avram_gaussianB_full_GH_mesh_energy_cauchy_of_source_linear_isometry_and_quadratic_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T00:56:03.117365+00:00
-- url     : https://prove2.me/submissions/d4b20dd9-ade9-4539-9dea-4b58885fcfbe

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_avram_gaussianB_quadratic_grid_L2_rate_forces_zero_energy
import Theorems.Thm_AvramDividend_Classical_avram_gaussianB_original_two_channel_L2_mesh_second_moment_cauchy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory AvramDividend.Classical
open scoped Topology
noncomputable section
/-- Exact original stopped Gaussian G/H physical-grid L2 assembly from B64, B239 and gb28. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (L Q : ℕ → Ω → ℝ) (K : ℕ × ℕ → ℝ)
    (σ C : ℝ) (hC : 0 ≤ C)
    (hLInt : ∀ m l, Integrable (fun ω => (L m ω - L l ω) ^ 2) P)
    (hQInt : ∀ m, Integrable (fun ω => (Q m ω) ^ 2) P)
    (hMInt : ∀ m l, Integrable (fun ω =>
      ((L m ω + Q m ω) - (L l ω + Q l ω)) ^ 2) P)
    (hLISO : ∀ m l,
      (∫ ω, (L m ω - L l ω) ^ 2 ∂P) = σ ^ 2 * K (m, l))
    (hK : Tendsto K atTop (𝓝 (0 : ℝ)))
    (hQNonneg : ∀ m, 0 ≤ ∫ ω, (Q m ω) ^ 2 ∂P)
    (hQRate : ∀ m,
      (∫ ω, (Q m ω) ^ 2 ∂P) ≤ C / ((m + 1 : ℕ) : ℝ)) :
    Tendsto (fun nm : ℕ × ℕ =>
      ∫ ω, ((L nm.1 ω + Q nm.1 ω) -
        (L nm.2 ω + Q nm.2 ω)) ^ 2 ∂P)
      atTop (𝓝 (0 : ℝ)) := by
  have hLEnergy :
      Tendsto (fun nm : ℕ × ℕ =>
        ∫ ω, (L nm.1 ω - L nm.2 ω) ^ 2 ∂P)
        atTop (𝓝 (0 : ℝ)) := by
    have hEq :
        (fun nm : ℕ × ℕ =>
          ∫ ω, (L nm.1 ω - L nm.2 ω) ^ 2 ∂P) =
        (fun nm : ℕ × ℕ => σ ^ 2 * K nm) := by
      funext nm
      exact hLISO nm.1 nm.2
    rw [hEq]
    simpa only [mul_zero] using hK.const_mul (σ ^ 2)
  have hQEnergy :
      Tendsto (fun m =>
        ∫ ω, (Q m ω) ^ 2 ∂P) atTop (𝓝 (0 : ℝ)) :=
    avram_gaussianB_quadratic_grid_L2_rate_forces_zero_energy
      C hC (fun m => ∫ ω, (Q m ω) ^ 2 ∂P)
      hQNonneg hQRate
  exact avram_gaussianB_original_two_channel_L2_mesh_second_moment_cauchy
    P L Q hLInt hQInt hMInt hLEnergy hQEnergy
