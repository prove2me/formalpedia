-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_jump8_original_frozen_prefix_path_filtration_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T19:19:25.046979+00:00
-- url     : https://prove2.me/submissions/407890a3-8164-47d9-9281-bb24d5c0bddc

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) :
    Measurable[𝓕 T]
      (fun ω : Ω => fun t : ℝ≥0 => X.X (min t T) ω) := by
  have hc (t : ℝ≥0) :
      Measurable[𝓕 T] (fun ω : Ω => X.X (min t T) ω) := by
    exact (X.adapted (min t T)).mono
      (𝓕.mono (min_le_right t T)) le_rfl
  exact (@measurable_pi_iff Ω ℝ≥0 (fun _ : ℝ≥0 => ℝ)
    (𝓕 T) (fun _ => inferInstance)
    (fun ω : Ω => fun t : ℝ≥0 => X.X (min t T) ω)).2 hc
