-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_18_original_countable_clock_preexit_left_limit_uniform_band_bound_C2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T00:04:09.722577+00:00
-- url     : https://prove2.me/submissions/1cf58efe-32eb-4f12-817f-51993d4ddd24

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_right_continuous_grid_detection
import Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_countable_exterior_exit_iff_prefix_interior_of_detection
import Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_preexit_left_limit_closed_band_bound_C2

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (r : ℕ → ℝ≥0) (lower upper : ℝ)
    (hlower : 0 < lower)
    (hcap : ∀ y ∈ Set.Icc lower upper, ENNReal.ofReal y < C)
    (hgrid : ∀ (s t : ℝ≥0), s < t →
      ∀ U : Set ℝ≥0, U ∈ 𝓝[Set.Ici s] s →
        ∃ k, r k < t ∧ r k ∈ U) :
    ∀ (ω : Ω) (T : ℝ≥0),
      (T : WithTop ℝ≥0) ≤ (⨅ k : ℕ,
        if x + X.X (r k) ω - rightLimit D (r k) ω < lower ∨
            upper < x + X.X (r k) ω - rightLimit D (r k) ω
        then (r k : WithTop ℝ≥0) else ⊤) →
      ∀ t : ℝ≥0, 0 < t → t < T →
        ∃ l : ℝ,
          Tendsto (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω)
            (𝓝[<] t) (𝓝 l) ∧
          (lower ≤ l ∧ l ≤ upper) ∧
          (0 < l ∧ ENNReal.ofReal l < C) ∧
          ContDiffWithinAt ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} l := by
  have hdetect :=
    avram_wave7_18_original_right_continuous_grid_detection
      X x D hD r lower upper hgrid
  intro ω T hclock t ht htT
  have hband : ∀ s : ℝ≥0, s < t →
      lower ≤ x + X.X s ω - rightLimit D s ω ∧
        x + X.X s ω - rightLimit D s ω ≤ upper := by
    intro s hs
    have hprefix :=
      (avram_wave7_18_original_countable_exterior_exit_iff_prefix_interior_of_detection
        X x D hD r lower upper hdetect ω T).mpr hclock
    exact hprefix s (lt_trans hs htT)
  exact avram_wave7_18_original_preexit_left_limit_closed_band_bound_C2
    X x D hD C w hw lower upper hlower hcap ω t ht hband
