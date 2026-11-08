-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual10_original_weighted_grid_residual_zero_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T22:42:25.951192+00:00
-- url     : https://prove2.me/submissions/907ed8b6-e4ab-48eb-bda9-0ab32875c13d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux11_original_BV_raw_removed_residual_zero_ae

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Every weighted finite-grid residual term vanishes for the original
bounded-variation Levy process, with no predictability or mesh assumptions. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (u : ℕ → ℕ → ℝ≥0) (A : ℕ → Ω → ℕ → ℝ) :
    ∀ᵐ ω ∂P, ∀ n : ℕ,
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) - J t
      ∑ i ∈ Finset.range (n + 1),
        A n ω i * (R (u n i) - R (u n (i + 1))) = 0 := by
  filter_upwards [avram_redux11_original_BV_raw_removed_residual_zero_ae
    X hX hBV] with ω hω
  intro n
  let J : ℝ≥0 → ℝ := fun t =>
    ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
      Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
    else 0
  let R : ℝ≥0 → ℝ := fun t =>
    ((t : ℝ) * X.drift - X.X t ω) - J t
  have hR (t : ℝ≥0) : R t = 0 := hω t
  apply Finset.sum_eq_zero
  intro i hi
  change A n ω i * (R (u n i) - R (u n (i + 1))) = 0
  rw [hR (u n i), hR (u n (i + 1))]
  ring
