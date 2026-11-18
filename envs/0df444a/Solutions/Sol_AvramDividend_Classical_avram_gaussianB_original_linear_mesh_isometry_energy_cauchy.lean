-- Prove2me | solution 1 for AvramDividend.Classical.avram_gaussianB_original_linear_mesh_isometry_energy_cauchy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T00:53:20.980973+00:00
-- url     : https://prove2.me/submissions/e9cbc738-bfc3-4050-922d-c31360a5ec8e

import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory
open scoped Topology
noncomputable section
/-- Transfer original Gaussian linear martingale isometry to two-mesh moment Cauchy. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (L : ℕ → Ω → ℝ) (K : ℕ × ℕ → ℝ) (σ : ℝ)
    (hIso : ∀ m l,
      (∫ ω, (L m ω - L l ω) ^ 2 ∂P) =
        σ ^ 2 * K (m, l))
    (hK : Tendsto K atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun nm : ℕ × ℕ =>
      ∫ ω, (L nm.1 ω - L nm.2 ω) ^ 2 ∂P)
      atTop (𝓝 (0 : ℝ)) := by
  have hEq :
      (fun nm : ℕ × ℕ =>
        ∫ ω, (L nm.1 ω - L nm.2 ω) ^ 2 ∂P) =
      (fun nm : ℕ × ℕ => σ ^ 2 * K nm) := by
    funext nm
    exact hIso nm.1 nm.2
  rw [hEq]
  simpa only [mul_zero] using hK.const_mul (σ ^ 2)
