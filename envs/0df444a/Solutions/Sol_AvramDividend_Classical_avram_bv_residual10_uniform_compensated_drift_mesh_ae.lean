-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual10_uniform_compensated_drift_mesh_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T22:22:39.029085+00:00
-- url     : https://prove2.me/submissions/e62533c8-ae29-4a74-99a5-e41dc08982a6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux11_original_BV_raw_removed_residual_zero_ae
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_uniform_compensated_drift_mesh

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original BV Levy jump representation makes every compensated
uniform physical-grid increment exactly a drift cell, almost surely. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (T : ℝ) (hT : 0 < T)
    (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i,
      (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2)) :
    ∀ᵐ ω ∂P,
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0
      let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
      (∀ n i, Y (u n (i + 1)) - Y (u n i) =
        X.drift * (T / ((n : ℝ) + 2))) ∧
      (∀ δ : ℝ, 0 < δ →
        ∀ᶠ n in atTop, ∀ i,
          |Y (u n (i + 1)) - Y (u n i)| < δ) := by
  filter_upwards [avram_redux11_original_BV_raw_removed_residual_zero_ae
    X hX hBV] with ω hω
  have hpath (t : ℝ≥0) :
      ((t : ℝ) * X.drift - X.X t ω) =
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0 := sub_eq_zero.mp (hω t)
  exact avram_bv_residual10_original_uniform_compensated_drift_mesh
    X ω hpath T hT u huniform
