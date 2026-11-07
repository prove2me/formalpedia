-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_jump8_original_frozen_prefix_jump_delta_agree
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T23:08:27.102959+00:00
-- url     : https://prove2.me/submissions/54be9f8d-50a8-4265-8e91-bc7a91a22eb9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_frozen_prefix_leftLim_before_stop
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (n : ℕ) (u : ℝ≥0) (hu : 0 < u) (huN : u ≤ (n : ℝ≥0)) :
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u =
    X.X (min u (n : ℝ≥0)) ω -
      Function.leftLim (fun v : ℝ≥0 => X.X (min v (n : ℝ≥0)) ω) u := by
  rw [min_eq_left huN,
    avram_wave7_06_original_frozen_prefix_leftLim_before_stop
      X ω (n : ℝ≥0) u hu huN]
