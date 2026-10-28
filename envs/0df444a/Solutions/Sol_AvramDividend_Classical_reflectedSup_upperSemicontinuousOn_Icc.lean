-- Prove2me | solution 1 for AvramDividend.Classical.reflectedSup_upperSemicontinuousOn_Icc
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T17:50:56.931912+00:00
-- url     : https://prove2.me/submissions/f4b6a5d7-fcc6-4046-9571-0671a737fb87

import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_cadlag_no_downward_jumps_upperSemicontinuousOn_Icc
import Theorems.Thm_AvramDividend_Classical_reflectedSup_right_continuous
import Theorems.Thm_AvramDividend_Classical_reflectedSup_leftLimit_actual
import Theorems.Thm_AvramDividend_Classical_reflectedSup_no_downward_jumps_actual
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Semicontinuity.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Topology Filter
open scoped NNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (ζ : ℝ≥0) :
    UpperSemicontinuousOn
      (fun t : ℝ≥0 => reflectedSup X t ω) (Icc 0 ζ) := by
  exact cadlag_no_downward_jumps_upperSemicontinuousOn_Icc
    (fun t : ℝ≥0 => reflectedSup X t ω) ζ
    (fun t => reflectedSup_right_continuous X ω t)
    (fun t ht => reflectedSup_leftLimit_actual X ω t ht)
    (fun t l ht hleft =>
      reflectedSup_no_downward_jumps_actual X ω t l ht hleft)
