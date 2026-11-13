-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a27_original_path_terminal_increment_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T08:49:43.329099+00:00
-- url     : https://prove2.me/submissions/6a8c1963-0061-43bb-874b-44c3442400eb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top12_original_zero_nu_capped_path_uniform_continuity
import Theorems.Thm_AvramDividend_Classical_avram_ga_a27_prehorizon_grid_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_ga_a27_prehorizon_grid_le
import Theorems.Thm_AvramDividend_Classical_avram_ga_a27_continuous_last_increment
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (n : ℝ≥0) :
    ∀ᵐ ω ∂P, Tendsto (fun m : ℕ =>
      X.X n ω - X.X ((m : ℝ≥0) * (n / ((m : ℝ≥0) + 1))) ω)
      atTop (nhds (0 : ℝ)) := by
  have hc := avram_ubv_top12_original_zero_nu_capped_path_uniform_continuity
    X hν n
  filter_upwards [hc] with ω hω
  apply avram_ga_a27_continuous_last_increment
    (fun t => X.X t ω) (Set.Icc 0 n) n
    (fun m : ℕ => (m : ℝ≥0) * (n / ((m : ℝ≥0) + 1)))
  · exact hω.continuousOn.continuousWithinAt (by simp)
  · exact avram_ga_a27_prehorizon_grid_tendsto n
  · exact Filter.Eventually.of_forall (fun m =>
      ⟨by simp, avram_ga_a27_prehorizon_grid_le n m⟩)
