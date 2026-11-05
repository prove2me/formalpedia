-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_positive_horizon_pair_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T18:48:36.61064+00:00
-- url     : https://prove2.me/submissions/48b92c85-98a0-4581-bc7a-7b3d62723a19

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_physical_ceil_pair_measurable_all_grid
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_uniform_ceil_pair_lintegral_limit
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_pair_mean_two_source_gaps

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology BigOperators
noncomputable section

/-- Close the original marked chronological pair moment from genuine finite-grid source expectation and measurability. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    let F : Ω → Finset ℝ≥0 := fun ω =>
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    let K : Ω → ℕ := fun ω =>
      ((F ω ×ˢ F ω).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card
    let r : ℝ :=
      (((T : ℝ≥0) : ℝ≥0∞) *
        X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    Integrable (fun ω => 2 * (K ω : ℝ)) P ∧
    (∫ ω, 2 * (K ω : ℝ) ∂P) = r ^ 2 := by
  classical
  have hMeas :=
    avram_p4_f_assembly_original_physical_ceil_pair_measurable_all_grid
      X T hT n
  have hLimit :=
    avram_p4_f_assembly_original_uniform_ceil_pair_lintegral_limit
      X T hT n
  simpa only using
    (avram_p4_f_assembly_original_pair_mean_two_source_gaps
      X T hT n hMeas hLimit)
