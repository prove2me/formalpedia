-- Prove2me | solution 1 for AvramDividend.Classical.avram_a22_original_zero_nu_every_positive_time_no_actual_jump_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T12:58:58.370135+00:00
-- url     : https://prove2.me/submissions/2d7babe5-2686-4dd2-95f5-875e684a4b34

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top11_original_zero_nu_global_continuous_ae
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The original Lévy source is physically jump-free on the full-measure continuous-path event. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0) :
    ∀ᵐ ω ∂P, ∀ u : ℝ≥0, 0 < u →
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0 := by
  filter_upwards [avram_ubv_top11_original_zero_nu_global_continuous_ae X hν]
    with ω hContinuous
  intro u _hu
  have hAt : ContinuousWithinAt (fun v : ℝ≥0 => X.X v ω) (Iic u) u :=
    (hContinuous.continuousAt).continuousWithinAt
  have hLeft : Function.leftLim (fun v : ℝ≥0 => X.X v ω) u =
      X.X u ω := hAt.leftLim_eq
  rw [hLeft]
  ring
