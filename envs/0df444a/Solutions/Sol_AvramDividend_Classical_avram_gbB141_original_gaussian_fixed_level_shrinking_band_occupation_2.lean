-- Prove2me | solution 2 for AvramDividend.Classical.avram_gbB141_original_gaussian_fixed_level_shrinking_band_occupation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:11:15.444505+00:00
-- url     : https://prove2.me/submissions/e5167e73-f1bc-4d46-8df1-905d170dedd6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB100_original_gaussian_fixed_level_occupation_null
import Theorems.Thm_AvramDividend_Classical_avram_gbB269_original_postpayment_reserve_joint_time_sample_measurable
import Theorems.Thm_AvramDividend_Classical_avram_gbB194_shrinking_band_from_null_level_measurable_path
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Shrinking original Gaussian reserve-level bands have vanishing occupation time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (x b : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ) (ρ : Ω → ℝ≥0) :
    ∀ᵐ ω ∂P,
      Tendsto (fun k : ℕ =>
        volume {t : ℝ |
          0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ) ∧
          abs (x + X.X (Real.toNNReal t) ω -
            rightLimit D (Real.toNNReal t) ω - b) <
              (1 : ℝ) / ((k : ℝ) + 1)})
        atTop (𝓝 (0 : ℝ≥0∞)) := by
  have hnull :=
    avram_gbB100_original_gaussian_fixed_level_occupation_null
      X hBV hν x b D hD n ρ
  filter_upwards [hnull] with ω hω
  have hf : Measurable (fun t : ℝ =>
      x + X.X (Real.toNNReal t) ω -
        rightLimit D (Real.toNNReal t) ω) := by
    exact (avram_gbB269_original_postpayment_reserve_joint_time_sample_measurable
      X x D hD).comp
        (measurable_real_toNNReal.prodMk measurable_const)
  exact avram_gbB194_shrinking_band_from_null_level_measurable_path
    (fun t : ℝ => x + X.X (Real.toNNReal t) ω -
      rightLimit D (Real.toNNReal t) ω) hf n (ρ ω : ℝ) b hω
