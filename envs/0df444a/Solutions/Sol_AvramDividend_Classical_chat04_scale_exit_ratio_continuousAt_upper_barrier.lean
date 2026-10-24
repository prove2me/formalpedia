-- Prove2me | solution 1 for AvramDividend.Classical.chat04_scale_exit_ratio_continuousAt_upper_barrier
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T16:45:23.591656+00:00
-- url     : https://prove2.me/submissions/a4144382-657a-4a7a-a8f5-fe94635080f4

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_continuousAt_away_zero
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Defs.Filter

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal

/-- The scale ratio is continuous in a strictly positive upper barrier. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (x a : ℝ) (ha : 0 < a) :
    ContinuousAt (fun b : ℝ => W x / W b) a := by
  have hWa : W a ≠ 0 := ne_of_gt
    (scaleFunction_strict_pos_of_standing X hX q hq W hW a ha)
  have hWcont : ContinuousAt W a :=
    scaleFunction_continuousAt_away_zero X q W hW a (ne_of_gt ha)
  exact continuousAt_const.div hWcont hWa
