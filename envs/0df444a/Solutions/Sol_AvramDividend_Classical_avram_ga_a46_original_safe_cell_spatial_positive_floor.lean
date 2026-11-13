-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a46_original_safe_cell_spatial_positive_floor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T23:54:32.893882+00:00
-- url     : https://prove2.me/submissions/65a162b9-30a3-4139-99d9-cd2f78c0e444

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gledger87_original_strict_rightlimit_le_later_dividend
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal

-- Every original strictly pre-stop full-cell spatial endpoint inherits the actual positive reserve floor.
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ρ : Ω → ℝ≥0) (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, s < t →
      0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤
        x + X.X t ω - rightLimit D s ω := by
  filter_upwards [hprefix] with ω hω
  intro s t hst ht htrho
  have hRisk := hω t ht htrho
  have hDividend :=
    avram_gledger87_original_strict_rightlimit_le_later_dividend
      D hD ω s t hst
  change (1 : ℝ) / ((j : ℝ) + 1) ≤ x + X.X t ω - D t ω at hRisk
  linarith
