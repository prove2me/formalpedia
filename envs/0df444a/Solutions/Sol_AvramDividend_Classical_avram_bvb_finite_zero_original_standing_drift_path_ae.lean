-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_finite_zero_original_standing_drift_path_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T00:07:30.756214+00:00
-- url     : https://prove2.me/submissions/62b3a15a-4f05-48f1-b96f-6a67cf686eff

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_finite_zero_original_negative_mark_count_zero_ae
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys75_original_zero_negative_mark_count_entire_source_drift
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hZero : X.ν (Iio (0 : ℝ)) = 0) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      X.X t ω = (t : ℝ) * X.drift := by
  have hEach (n : ℕ) :
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) →
        X.X t ω = (t : ℝ) * X.drift := by
    filter_upwards [
      AvramDividend.Classical.avram_bvb_finite_zero_original_negative_mark_count_zero_ae
        X hZero (n : ℝ≥0),
      AvramDividend.Classical.avram_bvb_phys75_original_zero_negative_mark_count_entire_source_drift
        X hX hBV (n : ℝ≥0)] with ω hc hp
    exact hp hc
  have hAll : ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ t : ℝ≥0,
      t ≤ (n : ℝ≥0) → X.X t ω = (t : ℝ) * X.drift := by
    exact MeasureTheory.ae_all_iff.mpr hEach
  filter_upwards [hAll] with ω hω t
  obtain ⟨n, hn⟩ := exists_nat_ge t
  exact hω n t hn
