-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_corrected_exit_high_barrier_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T21:48:40.615999+00:00
-- url     : https://prove2.me/submissions/ab4679e5-9b52-4f3a-86f9-d454e3cbddde

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_two_sided_exit_before_ruin_identity_corrected
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_scale_exit_ratio_tendsto_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- Genuine discounted original-clock two-sided upcrossing reward
vanishes when the target barrier tends to infinity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (hx : 0 ≤ x) :
    Tendsto (fun a : ℝ => twoSidedExitExpectationCorrected X q a x)
      atTop (𝓝 (0 : ENNReal)) := by
  have hscale :=
    avram_wave3_02_scale_exit_ratio_tendsto_zero X hX q hq W hW x
  have hlimit : Tendsto (fun a : ℝ => ENNReal.ofReal (W x / W a))
      atTop (𝓝 (0 : ENNReal)) := by
    have hcomp := (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hscale
    change Tendsto (fun a : ℝ => ENNReal.ofReal (W x / W a))
      atTop (𝓝 (ENNReal.ofReal (0 : ℝ))) at hcomp
    simpa only [ENNReal.ofReal_zero] using hcomp
  have hevent : ∀ᶠ a : ℝ in atTop,
      twoSidedExitExpectationCorrected X q a x =
      ENNReal.ofReal (W x / W a) := by
    filter_upwards [eventually_gt_atTop (max x 0)] with a ha
    have hpos : 0 < a := lt_of_le_of_lt (le_max_right x 0) ha
    have hxa : x ≤ a := le_of_lt (lt_of_le_of_lt (le_max_left x 0) ha)
    exact two_sided_exit_before_ruin_identity_corrected X hX q hq W hW
      a x hpos hx hxa
  have hevent' : (fun a : ℝ => ENNReal.ofReal (W x / W a)) =ᶠ[atTop]
      (fun a : ℝ => twoSidedExitExpectationCorrected X q a x) := by
    filter_upwards [hevent] with a ha
    exact ha.symm
  exact hlimit.congr' hevent'
