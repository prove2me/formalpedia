-- Prove2me | solution 1 for AvramDividend.Classical.avram_route_finite_t3_original_all_rows_positive_prejump_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T10:53:10.695914+00:00
-- url     : https://prove2.me/submissions/f6a49ebd-4f0b-4322-a800-930655c88d08

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_stieltjes10_original_countable_positive_grid_prejump
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Countable positive-time pre-payment identity across all physical-grid rows. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (u : ℕ → ℕ → ℝ≥0)
    (hu : ∀ n i, 0 < u n (i + 1)) :
    ∀ᵐ ω ∂P, ∀ n i,
      Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω)
        (u n (i + 1)) =
      riskProcess X x D (u n (i + 1)) ω := by
  rw [MeasureTheory.ae_all_iff]
  intro n
  exact avram_bv_stieltjes10_original_countable_positive_grid_prejump
    X x D hD (fun i => u n (i + 1)) (hu n)
