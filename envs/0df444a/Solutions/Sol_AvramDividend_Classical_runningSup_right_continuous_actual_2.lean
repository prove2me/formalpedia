-- Prove2me | solution 2 for AvramDividend.Classical.runningSup_right_continuous_actual
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T07:33:47.19875+00:00
-- url     : https://prove2.me/submissions/25dca49f-a35b-4bdf-88ad-40451cedecdd

import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_rawSup_nonneg
import Theorems.Thm_AvramDividend_Classical_runningSup_right_continuous_of_right_continuous

open AvramDividend.Classical MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (t : ℝ≥0) :
    ContinuousWithinAt (fun s : ℝ≥0 => runningSup X s ω) (Ici t) t := by
  exact runningSup_right_continuous_of_right_continuous (fun s => X.X s ω) (fun s => runningSup X s ω)
    (runningSup_monotone_and_path_le X ω).1 (runningSup_monotone_and_path_le X ω).2
    (fun s => (runningSup_eq_rawSup_nonneg X s ω).1) (fun s => X.rightCont ω s) t
