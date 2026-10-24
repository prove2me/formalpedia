-- Prove2me | solution 1 for AvramDividend.Classical.causal_continuous_kernel_reflection_ae_measurable_on_left_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T15:14:05.695601+00:00
-- url     : https://prove2.me/submissions/0fb471d4-34a9-4484-a473-933ac8703162

import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- Positive-time continuity survives reflection over a separated causal cutoff. -/
theorem solution
    (κ : ℝ → ℝ) (hκ : ContinuousOn κ (Ioi (0 : ℝ)))
    (x u : ℝ) (hu : 0 < u) (hux : u < x) :
    AEStronglyMeasurable (fun s : ℝ => κ (x - s))
      (volume.restrict (Ioc (0 : ℝ) u)) := by
  have hsub : Continuous (fun s : ℝ => x - s) :=
    continuous_const.sub continuous_id
  have hmap : MapsTo (fun s : ℝ => x - s) (Ioc (0 : ℝ) u) (Ioi 0) := by
    intro s hs
    exact sub_pos.mpr (lt_of_le_of_lt hs.2 hux)
  have hcont : ContinuousOn (fun s : ℝ => κ (x - s)) (Ioc (0 : ℝ) u) :=
    hκ.comp hsub.continuousOn hmap
  exact hcont.aestronglyMeasurable measurableSet_Ioc
