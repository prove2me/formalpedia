-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB229_original_floor_lower_cutoff_shrinking_occupation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T08:22:05.360141+00:00
-- url     : https://prove2.me/submissions/5d10c448-c2b9-42af-9b5b-f89a83b094bd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_postpayment_reserve_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_gbB228_original_floor_forces_lower_clip_level_null_occupation
import Theorems.Thm_AvramDividend_Classical_avram_gbB194_shrinking_band_from_null_level_measurable_path
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original strictly positive reserve floor eliminates all lower cutoff occupation bands. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ) (ρ : Ω → ℝ≥0) (δ : ℝ) (hδ : 0 < δ)
    (hFloor : ∀ ω (t : ℝ≥0), 0 < t → t < ρ ω →
      δ ≤ riskProcess X x D t ω) :
    ∀ ω : Ω,
      Tendsto (fun k : ℕ =>
        volume {t : ℝ |
          0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ) ∧
          abs (x + X.X (Real.toNNReal t) ω -
            rightLimit D (Real.toNNReal t) ω - δ / 2) <
            (1 : ℝ) / ((k : ℝ) + 1)})
        atTop (𝓝 (0 : ℝ≥0∞)) := by
  intro ω
  have hJoint :
      Measurable (fun z : ℝ≥0 × Ω =>
        x + X.X z.1 z.2 - rightLimit D z.1 z.2) := by
    simpa using
      (avram_wave8_20_original_postpayment_reserve_joint_measurable
        X x D hD)
  have hTime :
      Measurable (fun t : ℝ => (Real.toNNReal t, ω)) :=
    continuous_real_toNNReal.measurable.prodMk measurable_const
  have hf :
      Measurable (fun t : ℝ =>
        x + X.X (Real.toNNReal t) ω -
          rightLimit D (Real.toNNReal t) ω) :=
    hJoint.comp hTime
  exact
    avram_gbB194_shrinking_band_from_null_level_measurable_path
      (fun t : ℝ =>
        x + X.X (Real.toNNReal t) ω -
          rightLimit D (Real.toNNReal t) ω)
      hf n (ρ ω : ℝ) (δ / 2)
      (avram_gbB228_original_floor_forces_lower_clip_level_null_occupation
        X x D hD n ρ δ hδ hFloor ω)

