-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_right_continuous_below_barrier
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T10:18:17.422865+00:00
-- url     : https://prove2.me/submissions/8cb12f05-ae08-4c55-934d-9e827147d334

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_right_continuous
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_eq_thresholded_self_below_barrier

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hx : 0 ≤ x) (ha : 0 ≤ a) (hxa : x ≤ a) :
    ∀ ω (t : ℝ≥0),
      ContinuousWithinAt (fun s => barrierStrategy X x a s ω) (Ici t) t := by
  intro ω t
  have hbase :
      ContinuousWithinAt
        (fun s : ℝ≥0 => barrierStrategy X a a s ω) (Ici t) t :=
    AvramDividend.Classical.barrierStrategy_right_continuous X a ω t
  have hzero :
      ContinuousWithinAt (fun _ : ℝ≥0 => (0 : ℝ)) (Ici t) t :=
    continuousWithinAt_const
  have hoff :
      ContinuousWithinAt (fun _ : ℝ≥0 => a - x) (Ici t) t :=
    continuousWithinAt_const
  have hsub :
      ContinuousWithinAt
        (fun s : ℝ≥0 => barrierStrategy X a a s ω - (a - x))
        (Ici t) t := hbase.sub hoff
  have htrans :
      ContinuousWithinAt
        (fun s : ℝ≥0 => max 0 (barrierStrategy X a a s ω - (a - x)))
        (Ici t) t := hzero.max hsub
  simpa only [
    AvramDividend.Classical.barrierStrategy_eq_thresholded_self_below_barrier
      X x a hx ha hxa
  ] using htrans
