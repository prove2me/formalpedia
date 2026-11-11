-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva20_original_BV_uniform_R_cell_sum_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T23:39:33.810133+00:00
-- url     : https://prove2.me/submissions/1d288cd4-ff2f-412a-89e8-c682a9f7c9b0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux11_original_BV_raw_removed_residual_zero_ae
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/- The original BV pathwise drift residual is zero simultaneously at
   every time, so every finite physical-grid weighted R increment is zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (u : ℕ → ℕ → ℝ≥0) (A : ℕ → ℕ → Ω → ℝ) :
    ∀ᵐ ω ∂P, ∀ n : ℕ,
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) - J t
      (∑ i ∈ Finset.range (n + 1),
        A n i ω * (R (u n i) - R (u n (i + 1)))) = 0 := by
  classical
  filter_upwards
    [avram_redux11_original_BV_raw_removed_residual_zero_ae X hX hBV]
    with ω hzero
  intro n
  dsimp
  simp [hzero]
