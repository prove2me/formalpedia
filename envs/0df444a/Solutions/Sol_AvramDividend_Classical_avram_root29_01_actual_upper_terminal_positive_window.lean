-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_01_actual_upper_terminal_positive_window
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T15:28:33.895119+00:00
-- url     : https://prove2.me/submissions/a9805ce1-e652-470b-b83e-9b8088933207

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_rightContinuous_negative_right_interval

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- At an actual positive-reserve upper exit, source right continuity
gives a positive-length calendar interval of lower-barrier survival. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (x : ℝ) (τ : ℝ≥0)
    (hcont : ContinuousWithinAt (fun s : ℝ≥0 => X.X s ω) (Set.Ici τ) τ)
    (hpositive : 0 < x + X.X τ ω) :
    ∃ δ : ℝ≥0, 0 < δ ∧
      ∀ s : ℝ≥0, τ ≤ s → s < τ + δ →
        0 ≤ x + X.X s ω := by
  have hneg : -(x + X.X τ ω) < 0 := by linarith
  have hcont' : ContinuousWithinAt
      (fun s : ℝ≥0 => -(x + X.X s ω)) (Set.Ici τ) τ := by
    exact (continuousWithinAt_const.add hcont).neg
  obtain ⟨u, hu, hbelow⟩ :=
    rightContinuous_negative_right_interval
      (fun s : ℝ≥0 => -(x + X.X s ω)) τ hcont' hneg
  refine ⟨u - τ, tsub_pos_iff_lt.mpr hu, ?_⟩
  intro s hs hsu
  have hslt : s < u := by
    simpa only [add_tsub_cancel_of_le hu.le] using hsu
  have hneg_s := hbelow s hs hslt
  linarith
