-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB234_original_floor_two_cutoff_shrinking_union_from_upper_null
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T08:38:16.7852+00:00
-- url     : https://prove2.me/submissions/d2f8221e-23cf-4cd4-b910-c1a6f7108462
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB100_original_gaussian_fixed_level_occupation_null
import Theorems.Thm_AvramDividend_Classical_avram_gbB228_original_floor_forces_lower_clip_level_null_occupation
import Theorems.Thm_AvramDividend_Classical_avram_gbB223_two_null_levels_shrinking_union_occupation
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_postpayment_reserve_joint_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Only the prescribed upper clipping level needs Gaussian stochastic occupation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (x b : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ) (ρ : Ω → ℝ≥0) (δ : ℝ) (hδ : 0 < δ)
    (hFloor : ∀ ω (t : ℝ≥0), 0 < t → t < ρ ω →
      δ ≤ riskProcess X x D t ω) :
    ∀ᵐ ω ∂P,
      Tendsto (fun k : ℕ =>
        volume {t : ℝ |
          0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ) ∧
          (abs (x + X.X (Real.toNNReal t) ω -
            rightLimit D (Real.toNNReal t) ω - δ / 2) <
              (1 : ℝ) / ((k : ℝ) + 1) ∨
           abs (x + X.X (Real.toNNReal t) ω -
            rightLimit D (Real.toNNReal t) ω - b) <
              (1 : ℝ) / ((k : ℝ) + 1))})
        atTop (𝓝 (0 : ℝ≥0∞)) := by
  have hUpper :=
    avram_gbB100_original_gaussian_fixed_level_occupation_null
      X hBV hν x b D hD n ρ
  have hJoint :
      Measurable (fun z : ℝ≥0 × Ω =>
        x + X.X z.1 z.2 - rightLimit D z.1 z.2) := by
    simpa using
      (avram_wave8_20_original_postpayment_reserve_joint_measurable X x D hD)
  filter_upwards [hUpper] with ω hUpperω
  let f : ℝ → ℝ := fun t =>
    x + X.X (Real.toNNReal t) ω -
      rightLimit D (Real.toNNReal t) ω
  have hf : Measurable f := by
    exact hJoint.comp
      (continuous_real_toNNReal.measurable.prodMk measurable_const)
  have hLower :
      volume {t : ℝ |
        0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ) ∧
        f t = δ / 2} = 0 := by
    simpa only [f] using
      (avram_gbB228_original_floor_forces_lower_clip_level_null_occupation
        X x D hD n ρ δ hδ hFloor ω)
  have hUpper' :
      volume {t : ℝ |
        0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ) ∧ f t = b} = 0 := by
    simpa only [f] using hUpperω
  simpa only [f] using
    (avram_gbB223_two_null_levels_shrinking_union_occupation
      f hf n (ρ ω : ℝ) (δ / 2) b hLower hUpper')
