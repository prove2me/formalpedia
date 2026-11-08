-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid14_original_prejump_reserve_cofinal_band_bad_measure_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T16:47:17.150044+00:00
-- url     : https://prove2.me/submissions/f3fd08b5-b782-4268-ac73-fa4df73cefb4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_finite_clock_predictable_left_reserve_jointly_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid14_cofinal_band_bad_event_measure_tendsto_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Genuine pre-payment stopped-grid reserve observations exhaust cofinal
interior bands in probability, using the original predictable Lévy source. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (a b : ℕ → ℝ)
    (hExh : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      ∃ N : ℕ, ∀ k ≥ N, y ∈ Icc (a k) (b k))
    (n : ℕ) (u : ℕ → ℕ → ℝ≥0) :
    Tendsto (fun k : ℕ =>
      P ({ω : Ω | ∀ i < n + 1,
        (0 < Function.leftLim
          (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i) ∧
          ENNReal.ofReal (Function.leftLim
            (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)) < C) →
        Function.leftLim
          (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i) ∈
          Icc (a k) (b k)}ᶜ))
      atTop (𝓝 (0 : ℝ≥0∞)) := by
  let Z : Ω → ℕ → ℝ := fun ω i =>
    Function.leftLim
      (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
  have hZ (i : ℕ) : Measurable (fun ω : Ω => Z ω i) := by
    have hjoint :=
      avram_wave7_17_original_finite_clock_predictable_left_reserve_jointly_measurable
        X x D hD (u n i)
    have hfix : Measurable (fun ω : Ω => ((u n i), ω)) :=
      measurable_const.prodMk measurable_id
    have hcomp := hjoint.comp hfix
    convert hcomp using 1
    funext ω
    simp [Z]
  simpa only [Z] using
    (avram_p3_grid14_cofinal_band_bad_event_measure_tendsto_zero
      P C a b hExh n Z hZ)
