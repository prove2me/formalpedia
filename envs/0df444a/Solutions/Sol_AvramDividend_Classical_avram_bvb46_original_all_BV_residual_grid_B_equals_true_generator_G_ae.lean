-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb46_original_all_BV_residual_grid_B_equals_true_generator_G_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T12:42:26.322203+00:00
-- url     : https://prove2.me/submissions/8f0fdcc6-f4aa-4f8c-9c56-cffc25038f0f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bva22_original_all_BV_two_clock_source_increment_ae
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Exact original spectrally negative BV source increments make the full
physical R correction vanish in any finite weighted grid, without a no-jump
path premise or an artificial finite-activity reduction. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (u : ℕ → ℕ → ℝ≥0)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ t ω,
      R t ω = ((t : ℝ) * X.drift - X.X t ω) -
        (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω else 0))
    (coeff : ℕ → ℕ → Ω → ℝ)
    (B G : ℕ → Ω → ℝ)
    (hB : ∀ n ω, B n ω = G n ω +
      (∑ i ∈ Finset.range (n + 1),
        coeff n i ω * (R (u n i) ω - R (u n (i + 1)) ω))) :
    ∀ᵐ ω ∂P, ∀ n, B n ω = G n ω := by
  have hSource :=
    avram_bva22_original_all_BV_two_clock_source_increment_ae X hX hBV
  filter_upwards [hSource] with ω hω
  intro n
  rw [hB n ω]
  have hSum : (∑ i ∈ Finset.range (n + 1),
      coeff n i ω * (R (u n i) ω - R (u n (i + 1)) ω)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hPair := hω (u n i) (u n (i + 1))
    have hDiff : R (u n i) ω - R (u n (i + 1)) ω = 0 := by
      rw [hR (u n i) ω, hR (u n (i + 1)) ω]
      linear_combination hPair
    rw [hDiff, mul_zero]
  rw [hSum, add_zero]
