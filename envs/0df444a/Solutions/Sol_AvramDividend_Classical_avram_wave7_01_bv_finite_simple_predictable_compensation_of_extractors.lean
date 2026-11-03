-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_bv_finite_simple_predictable_compensation_of_extractors
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:18:52.78652+00:00
-- url     : https://prove2.me/submissions/0d872bbc-98eb-47a6-aa32-b544531e7798

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_bv_negative_mark_adapted_weight_compensation_of_extractor
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_shifted_future_path_coordinate_product_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Finite nonnegative predictable simple-jump compensation on the exact original source path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (S : Finset ℕ) (s t : ℕ → ℝ≥0)
    (hst : ∀ i ∈ S, s i ≤ t i)
    (H : ℕ → Ω → ℝ≥0∞)
    (hH : ∀ i ∈ S, Measurable[𝓕 (s i)] (H i))
    (F : ℕ → (ℝ≥0 → ℝ) → ℝ≥0∞)
    (hF : ∀ i ∈ S, Measurable (F i))
    (hExtract : ∀ i ∈ S, ∀ ω : Ω,
      ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc (s i) (t i) ×ˢ Iio (0 : ℝ)) =
        F i (fun v : ℝ≥0 => X.X (s i + v) ω - X.X (s i) ω)) :
    (∫⁻ ω, ∑ i ∈ S, H i ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc (s i) (t i) ×ˢ Iio (0 : ℝ)) ∂P) =
    ∑ i ∈ S,
      (∫⁻ ω, H i ω ∂P) *
        ((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) := by
  let N : ℕ → Ω → ℝ≥0∞ := fun i ω => ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc (s i) (t i) ×ˢ Iio (0 : ℝ))
  have hNMeas (i : ℕ) (hi : i ∈ S) : Measurable (N i) := by
    have hFuture := (hF i hi).comp
      (avram_wave7_01_original_shifted_future_path_coordinate_product_measurable
        X (s i))
    convert hFuture using 1
    funext ω
    exact hExtract i hi ω
  have hSummand (i : ℕ) (hi : i ∈ S) :
      Measurable (fun ω : Ω => H i ω * N i ω) := by
    have hHmeas : Measurable (H i) :=
      (hH i hi).mono (𝓕.le (s i)) le_rfl
    exact hHmeas.mul (hNMeas i hi)
  change (∫⁻ ω, ∑ i ∈ S, H i ω * N i ω ∂P) =
      ∑ i ∈ S, (∫⁻ ω, H i ω ∂P) *
        ((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ))
  rw [lintegral_finset_sum S hSummand]
  apply Finset.sum_congr rfl
  intro i hi
  change (∫⁻ ω, H i ω * N i ω ∂P) =
    (∫⁻ ω, H i ω ∂P) *
      ((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ))
  exact avram_wave7_01_bv_negative_mark_adapted_weight_compensation_of_extractor
    X hBV hFinite (s i) (t i) (hst i hi)
      (H i) (hH i hi) (F i) (hF i hi) (hExtract i hi)

