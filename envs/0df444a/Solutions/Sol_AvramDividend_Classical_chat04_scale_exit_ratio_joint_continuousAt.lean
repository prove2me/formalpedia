-- Prove2me | solution 1 for AvramDividend.Classical.chat04_scale_exit_ratio_joint_continuousAt
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T16:59:06.561708+00:00
-- url     : https://prove2.me/submissions/7761d71a-7fd5-4baa-9563-0a3d1a87eef9

import Mathlib.Topology.Constructions.SumProd
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_continuousAt_away_zero
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal

/-- Joint continuity of the q-scale ratio in strictly positive reserves and barriers. -/
theorem solution
{Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (x a : ℝ)
    (hx : 0 < x) (ha : 0 < a) :
    ContinuousAt (fun p : ℝ × ℝ => W p.1 / W p.2) (x, a) := by
  have hWx : ContinuousAt W x :=
    scaleFunction_continuousAt_away_zero X q W hW x (ne_of_gt hx)
  have hWa : ContinuousAt W a :=
    scaleFunction_continuousAt_away_zero X q W hW a (ne_of_gt ha)
  have hnum : ContinuousAt (fun p : ℝ × ℝ => W p.1) (x, a) :=
    hWx.comp continuousAt_fst
  have hden : ContinuousAt (fun p : ℝ × ℝ => W p.2) (x, a) :=
    hWa.comp continuousAt_snd
  have hpositive : W a ≠ 0 := ne_of_gt
    (scaleFunction_strict_pos_of_standing X hX q hq W hW a ha)
  exact hnum.div hden hpositive
