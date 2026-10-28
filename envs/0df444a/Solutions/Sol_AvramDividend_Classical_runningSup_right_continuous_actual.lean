-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_right_continuous_actual
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T07:32:06.987885+00:00
-- url     : https://prove2.me/submissions/f612fd8a-4c13-4fee-a27f-15b4ed6e6c48

import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_rawSup_nonneg
import Theorems.Thm_AvramDividend_Classical_runningSup_right_continuous_of_right_continuous
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Defs.Filter

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (t : ℝ≥0) :
    ContinuousWithinAt (fun s : ℝ≥0 => runningSup X s ω) (Ici t) t := by
  obtain ⟨hmono, hdom⟩ := runningSup_monotone_and_path_le X ω
  exact runningSup_right_continuous_of_right_continuous
    (fun s : ℝ≥0 => X.X s ω)
    (fun s : ℝ≥0 => runningSup X s ω)
    hmono hdom
    (fun s => (runningSup_eq_rawSup_nonneg X s ω).1)
    (fun s => X.rightCont ω s) t
