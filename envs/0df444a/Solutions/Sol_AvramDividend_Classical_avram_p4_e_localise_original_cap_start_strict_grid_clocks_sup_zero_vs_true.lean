-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_cap_start_strict_grid_clocks_sup_zero_vs_true
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:40:42.753932+00:00
-- url     : https://prove2.me/submissions/8da921e2-7372-4b79-8b0b-4a0fa072ca4f

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

/-- Every strict subcap grid clock is zero at an unpaid cap start, although true ruin can be later. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (c x : ℝ) (hc : 0 < c) (hxc : x = c)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (ω : Ω) (hNoInitialPayment : rightLimit D 0 ω = 0)
    (r : ℕ → ℕ → ℝ≥0) (hr0 : ∀ k, r k 0 = 0)
    (lower upper : ℕ → ℝ) (hUpper : ∀ k, upper k < c)
    (n : ℕ) (hn : 0 < n)
    (hRuinPos : 0 < ruinTime X x D ω) :
    (⨆ k : ℕ, min (⨅ j : ℕ,
      if x + X.X (r k j) ω - rightLimit D (r k j) ω < lower k ∨
         upper k < x + X.X (r k j) ω - rightLimit D (r k j) ω
      then (r k j : WithTop ℝ≥0) else ⊤) (n : WithTop ℝ≥0)) =
        (0 : WithTop ℝ≥0) ∧
    0 < (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal := by
  have hAll : ∀ k : ℕ,
      min (⨅ j : ℕ,
        if x + X.X (r k j) ω - rightLimit D (r k j) ω < lower k ∨
           upper k < x + X.X (r k j) ω - rightLimit D (r k j) ω
        then (r k j : WithTop ℝ≥0) else ⊤) (n : WithTop ℝ≥0) = 0 := by
    intro k
    exact avram_p4_e_localise_original_cap_start_inner_band_grid_exit_zero
      X c x hc hxc D hD ω hNoInitialPayment (r k) (hr0 k)
      (lower k) (upper k) (hUpper k) (n : ℝ≥0)
  constructor
  · simp only [hAll, iSup_const]
  · have hClockZeroIff :=
      avram_p4_e_localise_original_positive_horizon_zero_clock_iff_immediate_ruin
        X x D n hn ω
    have hClockNe :
        (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal ≠ 0 := by
      intro hZero
      exact (ne_of_gt hRuinPos) (hClockZeroIff.mp hZero)
    exact (pos_iff_ne_zero).mpr hClockNe
