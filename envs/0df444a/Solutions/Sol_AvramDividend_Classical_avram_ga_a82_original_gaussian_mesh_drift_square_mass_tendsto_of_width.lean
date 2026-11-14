-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a82_original_gaussian_mesh_drift_square_mass_tendsto_of_width
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T07:59:10.009339+00:00
-- url     : https://prove2.me/submissions/cce662da-4ec1-455e-ba89-9b0ed4114a41

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology AvramDividend.Classical
open scoped NNReal

/-- A bounded original physical mesh horizon and vanishing width force the total squared deterministic Gaussian drift energy to vanish. -/
theorem solution
    (n : ℕ) (Δ : ℕ → ℝ≥0)
    (hΔ : Tendsto (fun m : ℕ => (Δ m : ℝ)) atTop (𝓝 (0 : ℝ)))
    (hMass : ∀ m : ℕ, (m : ℝ) * (Δ m : ℝ) ≤ (n : ℝ))
    (c : ℝ) :
    Tendsto (fun m : ℕ =>
      (m : ℝ) * (((Δ m : ℝ) * c)^2))
        atTop (𝓝 (0 : ℝ)) := by
  have hUpper : Tendsto (fun m : ℕ =>
      (n : ℝ) * ((Δ m : ℝ) * c^2)) atTop (𝓝 (0 : ℝ)) := by
    have h := (hΔ.mul_const (c^2)).const_mul (n : ℝ)
    simpa only [zero_mul, mul_zero] using h
  have hLe (m : ℕ) :
      (m : ℝ) * (((Δ m : ℝ) * c)^2) ≤
        (n : ℝ) * ((Δ m : ℝ) * c^2) := by
    have hnonneg : 0 ≤ (Δ m : ℝ) * c^2 :=
      mul_nonneg (Δ m).property (sq_nonneg c)
    have hh := mul_le_mul_of_nonneg_right (hMass m) hnonneg
    nlinarith [hh]
  have hGe (m : ℕ) :
      (0 : ℝ) ≤ (m : ℝ) * (((Δ m : ℝ) * c)^2) :=
    mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hUpper
    (Filter.Eventually.of_forall hGe)
    (Filter.Eventually.of_forall hLe)
