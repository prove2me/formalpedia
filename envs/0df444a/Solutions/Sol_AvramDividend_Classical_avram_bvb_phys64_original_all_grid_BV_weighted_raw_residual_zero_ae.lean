-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys64_original_all_grid_BV_weighted_raw_residual_zero_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T23:20:04.828221+00:00
-- url     : https://prove2.me/submissions/43529287-01bb-4965-9113-993960fddb1f

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_redux11_original_BV_raw_removed_residual_zero_ae
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Every weighted physical-grid increment of the original BV raw
removed-jump residual vanishes, on a common full-measure set. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (u : ℕ → ℕ → ℝ≥0) (W : ℕ → Ω → ℕ → ℝ) :
    ∀ᵐ ω ∂P, ∀ n : ℕ,
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) - J t
      ∑ i ∈ Finset.range (n + 1),
        W n ω i * (R (u n i) - R (u n (i + 1))) = 0 := by
  have hzero :=
    avram_redux11_original_BV_raw_removed_residual_zero_ae X hX hBV
  filter_upwards [hzero] with ω hω
  intro n
  dsimp
  simp [hω]
