-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva88_original_marked_jump_zero_initial_fibre_without_meas_assumption
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T21:39:03.537213+00:00
-- url     : https://prove2.me/submissions/34157ce8-b30c-4307-a285-92ed83c06274

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_route_runner_f_original_frozen_mark_maps_any_horizon
import Theorems.Thm_AvramDividend_Classical_avram_bva85_original_marked_jump_measure_zero_initial_fibre
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (({0} : Set ℝ≥0) ×ˢ Set.univ) = 0 := by
  have hMeas :=
    (avram_route_runner_f_original_frozen_mark_maps_any_horizon
      X ω (0 : ℝ≥0)).1
  exact avram_bva85_original_marked_jump_measure_zero_initial_fibre X ω hMeas
