-- Prove2me | solution 1 for AvramDividend.Classical.avram_integration_sweep9_original_BV_interval_absolute_source_variation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T15:14:56.046007+00:00
-- url     : https://prove2.me/submissions/3b0a3f62-f3c5-44da-bc83-59c9e2c532d2

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_removed_residual_monotone
import Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_raw_J_monotone
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P,
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0
      let R : ℝ≥0 → ℝ := fun t => ((t : ℝ) * X.drift - X.X t ω) - J t
      ∀ s t : ℝ≥0, s ≤ t →
        |X.X t ω - X.X s ω| ≤
          |X.drift| * ((t : ℝ) - (s : ℝ)) +
          (R t - R s) + (J t - J s) := by
  filter_upwards
    [avram_p3_a_bvdrift_original_raw_removed_residual_monotone X hBV,
     avram_p3_f_chainlimit_original_raw_J_monotone X hBV] with ω hR hJ
  intro J R s t hst
  have hJnonneg : 0 ≤ J t - J s := sub_nonneg.mpr (hJ s t hst)
  have hRnonneg : 0 ≤ R t - R s := sub_nonneg.mpr (hR hst)
  have hstReal : (s : ℝ) ≤ (t : ℝ) := by
    exact_mod_cast hst
  have htime : 0 ≤ (t : ℝ) - (s : ℝ) := sub_nonneg.mpr hstReal
  have hident : X.X t ω - X.X s ω =
      X.drift * ((t : ℝ) - (s : ℝ)) -
        (J t - J s) - (R t - R s) := by
    dsimp [R]
    ring
  have htriangle (a b c : ℝ) :
      |a - b - c| ≤ |a| + |b| + |c| := by
    calc
      |a - b - c| = |(a + -b) + -c| := by ring
      _ ≤ |a + -b| + |-c| := abs_add_le _ _
      _ ≤ (|a| + |-b|) + |-c| := by
        exact add_le_add_left (abs_add_le a (-b)) |-c|
      _ = |a| + |b| + |c| := by simp
  have hAbs :
      |X.X t ω - X.X s ω| ≤
        |X.drift * ((t : ℝ) - (s : ℝ))| +
          |J t - J s| + |R t - R s| := by
    rw [hident]
    exact htriangle _ _ _
  rw [abs_mul, abs_of_nonneg htime, abs_of_nonneg hJnonneg,
    abs_of_nonneg hRnonneg] at hAbs
  linarith
