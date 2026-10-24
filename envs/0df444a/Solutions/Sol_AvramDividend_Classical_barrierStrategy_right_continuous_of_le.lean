-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_right_continuous_of_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T14:13:19.06392+00:00
-- url     : https://prove2.me/submissions/271bb938-9249-478f-abe9-fb5311c5487b

import Theorems.Thm_AvramDividend_Classical_barrierStrategy_right_continuous
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_offset_of_le
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Defs.Filter

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Every barrier dividend process started at or below its barrier is right-continuous. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hxa : x ≤ a) :
    ∀ ω (t : ℝ≥0),
      ContinuousWithinAt (fun s => barrierStrategy X x a s ω) (Ici t) t := by
  intro ω t
  have hbase :
      ContinuousWithinAt
        (fun s : ℝ≥0 => barrierStrategy X a a s ω) (Ici t) t :=
    barrierStrategy_right_continuous X a ω t
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
  simpa only [barrierStrategy_offset_of_le X x a hxa] using htrans
