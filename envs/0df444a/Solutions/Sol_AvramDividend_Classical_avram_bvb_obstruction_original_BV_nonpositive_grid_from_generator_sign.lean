-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_obstruction_original_BV_nonpositive_grid_from_generator_sign
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:44:19.85778+00:00
-- url     : https://prove2.me/submissions/631f9e64-d6f4-4569-b36a-c1eb8bb1e53c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bvb46_original_all_BV_residual_grid_B_equals_true_generator_G_ae
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
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
        coeff n i ω * (R (u n i) ω - R (u n (i + 1)) ω)))
    (hG : ∀ n ω, G n ω ≤ 0) :
    ∀ᵐ ω ∂P, ∀ n, B n ω ≤ 0 := by
  have hBG :=
    avram_bvb46_original_all_BV_residual_grid_B_equals_true_generator_G_ae
      X hX hBV u R hR coeff B G hB
  filter_upwards [hBG] with ω hω
  intro n
  rw [hω n]
  exact hG n ω
