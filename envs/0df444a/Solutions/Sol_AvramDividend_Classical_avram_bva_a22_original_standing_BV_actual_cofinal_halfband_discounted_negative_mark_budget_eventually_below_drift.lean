-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_a22_original_standing_BV_actual_cofinal_halfband_discounted_negative_mark_budget_eventually_below_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T11:13:25.998229+00:00
-- url     : https://prove2.me/submissions/2aca0c50-1d42-4143-b28f-455bde78c866

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_arbitrary_cofinal_positive_spatial_lower_band_tendsto_zero_without_rate
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_BV_any_shrinking_spatial_width_eventual_positive_physical_drift_after_negative_mark_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (C : ℝ≥0∞) (hC : 0 < C)
    (a b : ℕ → ℝ) (ha : ∀ n, 0 < a n)
    (ha2 : ∀ n, a n ≤ 2) (hab : ∀ n, a n ≤ b n)
    (hinside : ∀ n, Icc (a n / 2) (b n) ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hcover : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      ∃ N : ℕ, ∀ n ≥ N, y ∈ Icc (a n) (b n)) :
    ∀ᶠ n : ℕ in atTop,
      q * (a n / 2) +
        (∫ z in Iio (0 : ℝ), min (a n / 2) (-z) ∂X.ν) < X.drift := by
  have hA :=
    avram_bva_a22_original_arbitrary_cofinal_positive_spatial_lower_band_tendsto_zero_without_rate
      C hC a b ha hab hinside hcover
  have hd : 0 < X.drift := (bv_standing_drift_pos X hX hBV).1
  have hε : ∀ n, 0 < a n / 2 ∧ a n / 2 ≤ 1 := by
    intro n
    constructor <;> linarith [ha n, ha2 n]
  have hεzero : Tendsto (fun n => a n / 2)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [zero_div] using hA.div_const (2 : ℝ)
  exact avram_bva_a22_original_BV_any_shrinking_spatial_width_eventual_positive_physical_drift_after_negative_mark_budget
    X hBV hd q (fun n => a n / 2) hε hεzero
