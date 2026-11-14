-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb56_original_terminal_actual_count_zero_and_intensity_epsilon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:58:51.9477+00:00
-- url     : https://prove2.me/submissions/ee203db1-2ee4-402e-aba1-934f86f404e5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bvb51_original_uniform_last_horizon_source_negative_count_zero_ae
import Theorems.Thm_AvramDividend_Classical_avram_bvb52_original_finite_negative_rate_times_uniform_last_strip_width_zero
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
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ) (hT : 0 < T)
    (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i, (u n i : ℝ) =
      T * (i : ℝ) / ((n : ℝ) + 2)) :
    let S : ℝ≥0 := ⟨T,le_of_lt hT⟩
    ∀ ε : ℝ, 0 < ε →
      ∀ᵐ ω ∂P, ∀ᶠ n in (atTop : Filter ℕ),
      (Measure.count.restrict
        {t : ℝ≥0 | 0 < t ∧
          X.X t ω - Function.leftLim
            (fun s : ℝ≥0 => X.X s ω) t ≠ 0})
        (Ioc (u n (n + 1)) S) = 0 ∧
      (X.ν (Iio (0 : ℝ))).toReal *
        (T / ((n : ℝ) + 2)) < ε := by
  intro S ε hε
  have hCount :=
    avram_bvb51_original_uniform_last_horizon_source_negative_count_zero_ae
      X hBV hFinite T hT u huniform
  have hIntensity :=
    (avram_bvb52_original_finite_negative_rate_times_uniform_last_strip_width_zero
      X hFinite T hT).eventually (eventually_lt_nhds hε)
  filter_upwards [hCount] with ω hω
  exact hω.and hIntensity
