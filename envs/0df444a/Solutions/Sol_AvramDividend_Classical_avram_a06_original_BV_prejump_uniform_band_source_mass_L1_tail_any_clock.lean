-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_original_BV_prejump_uniform_band_source_mass_L1_tail_any_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T12:50:15.168895+00:00
-- url     : https://prove2.me/submissions/377b5322-bae5-4a33-97e1-4777ccdcff78

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_controlled_postpayment_prejump_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_comp8_original_BV_source_mass_integrable_any_clock
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_uniform_row_weighted_bad_band_expectation_vanish
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology Classical
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ≥0)
    (u : ℕ → ℕ → ℝ≥0) (n : ℕ)
    (a b : ℕ → ℝ)
    (hExh : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      ∃ N : ℕ, ∀ k ≥ N, y ∈ Icc (a k) (b k)) :
    Tendsto (fun k : ℕ =>
      ∫ ω, (if ∀ i < n + 1,
        (0 < Function.leftLim
            (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) (u n i) ∧
          ENNReal.ofReal (Function.leftLim
            (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) (u n i)) < C) →
        Function.leftLim
          (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) (u n i)
          ∈ Icc (a k) (b k) then (0 : ℝ)
        else |X.drift| * (T : ℝ) +
          |(T : ℝ) * X.drift - X.X T ω|) ∂P)
      atTop (𝓝 (0 : ℝ))  := by
  let Z : Ω → ℕ → ℝ := fun ω i =>
    Function.leftLim
      (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) (u n i)
  let H : Ω → ℝ := fun ω =>
    |X.drift| * (T : ℝ) + |(T : ℝ) * X.drift - X.X T ω|
  have hJoint :=
    avram_wave4_04b_controlled_postpayment_prejump_joint_measurable
      X x D hD.1.1
  have hZ (i : ℕ) : Measurable (fun ω => Z ω i) := by
    exact hJoint.comp (measurable_const.prodMk measurable_id)
  have hXt : Measurable (X.X T) :=
    (X.adapted T).mono (𝓕.le T) le_rfl
  have hHm : Measurable H :=
    measurable_const.add (measurable_const.sub hXt).abs
  have hHI : Integrable H P :=
    (avram_p3_comp8_original_BV_source_mass_integrable_any_clock
      X hX hBV T).1
  simpa only [Z, H] using
    (avram_a06_original_uniform_row_weighted_bad_band_expectation_vanish
      P C a b hExh n Z hZ H hHm hHI)
