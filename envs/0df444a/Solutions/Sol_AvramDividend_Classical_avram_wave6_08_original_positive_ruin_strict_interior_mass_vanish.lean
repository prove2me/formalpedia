-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_08_original_positive_ruin_strict_interior_mass_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T09:53:15.562341+00:00
-- url     : https://prove2.me/submissions/6b10e57f-cea0-408c-a1c5-fc82a3b62a9f

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_strict_interior_dividendMeasure_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_positive_ruin_strict_left_dividend_cell_vanish

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The genuine full strictly pre-ruin Stieltjes terminal cell vanishes,
including diffuse and atomic dividend mass but excluding the ruin right atom. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (τ : ℝ≥0) (hτ : 0 < τ)
    (u : ℕ → ℝ≥0) (hu : ∀ n, u n < τ)
    (hlim : Tendsto u atTop (𝓝 τ)) :
    Tendsto (fun n => dividendMeasure D ω (Ioo (u n : ℝ) (τ : ℝ)))
      atTop (𝓝 0) := by
  have hreal :
      Tendsto (fun n => D τ ω - rightLimit D (u n) ω) atTop (𝓝 0) :=
    avram_wave6_08_original_positive_ruin_strict_left_dividend_cell_vanish
      D hD ω τ hτ u hu hlim
  have hENN :
      Tendsto (fun n => ENNReal.ofReal (D τ ω - rightLimit D (u n) ω))
        atTop (𝓝 (ENNReal.ofReal 0)) :=
    (ENNReal.continuous_ofReal.tendsto 0).comp hreal
  have hcell (n : ℕ) :
      dividendMeasure D ω (Ioo (u n : ℝ) (τ : ℝ)) =
        ENNReal.ofReal (D τ ω - rightLimit D (u n) ω) :=
    avram_wave6_08_original_strict_interior_dividendMeasure_rightLimit
      D hD ω (u n) τ (hu n)
  simpa only [← hcell, ENNReal.ofReal_zero] using hENN
