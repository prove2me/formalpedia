-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_02_reflected_local_time_normalized_at_first_passage
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T16:05:56.850421+00:00
-- url     : https://prove2.me/submissions/a1f40ab8-242d-4b35-9fac-f9c81195d455

import Mathlib.Algebra.Group.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_attains_peak
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_runningSup_sub_path_eq_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (hb : 0 ≤ b) (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (t : ℝ≥0) (_ : b < X.X t ω), (t : ℝ≥0∞))) :
    runningSup X u ω = b ∧ reflectedSup X u ω = 0 := by
  have hpath : X.X u ω = b :=
    (firstUpcrossing_attains_peak X b hb ω u hu).1
  have hdraw : runningSup X u ω - X.X u ω = 0 :=
    firstUpcrossing_runningSup_sub_path_eq_zero X b hb ω u hu
  have hrecord : runningSup X u ω = X.X u ω := sub_eq_zero.mp hdraw
  constructor
  · exact hrecord.trans hpath
  · change runningSup X u ω - X.X u ω = 0
    exact hdraw
