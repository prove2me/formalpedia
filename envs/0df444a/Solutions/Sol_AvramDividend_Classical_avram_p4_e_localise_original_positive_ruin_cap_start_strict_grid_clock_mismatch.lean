-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_positive_ruin_cap_start_strict_grid_clock_mismatch
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:30:27.425404+00:00
-- url     : https://prove2.me/submissions/8bfd329f-d77e-4a0b-a4ee-59b552c33730

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_cap_start_inner_band_grid_exit_zero
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_positive_horizon_zero_clock_iff_immediate_ruin
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- At positive ruin an unpaid cap-start separates strict grid exit from the real ruin clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (c x : ℝ) (hc : 0 < c) (hxc : x = c)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (ω : Ω) (hNoInitialPayment : rightLimit D 0 ω = 0)
    (r : ℕ → ℝ≥0) (hr0 : r 0 = 0)
    (lower upper : ℝ) (hUpper : upper < c)
    (n : ℕ) (hn : 0 < n)
    (hRuinPos : 0 < ruinTime X x D ω) :
    min (⨅ k : ℕ,
      if x + X.X (r k) ω - rightLimit D (r k) ω < lower ∨
         upper < x + X.X (r k) ω - rightLimit D (r k) ω
      then (r k : WithTop ℝ≥0) else ⊤) (n : WithTop ℝ≥0) =
        (0 : WithTop ℝ≥0) ∧
    0 < (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal := by
  constructor
  · exact avram_p4_e_localise_original_cap_start_inner_band_grid_exit_zero
      X c x hc hxc D hD ω hNoInitialPayment r hr0
      lower upper hUpper (n : ℝ≥0)
  · have hClockZeroIff :=
      avram_p4_e_localise_original_positive_horizon_zero_clock_iff_immediate_ruin
        X x D n hn ω
    have hClockNe :
        (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal ≠ 0 := by
      intro hZero
      exact (ne_of_gt hRuinPos) (hClockZeroIff.mp hZero)
    exact (pos_iff_ne_zero).mpr hClockNe
