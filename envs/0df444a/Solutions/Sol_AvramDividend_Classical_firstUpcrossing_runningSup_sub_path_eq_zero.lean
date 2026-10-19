-- Prove2me | solution 1 for AvramDividend.Classical.firstUpcrossing_runningSup_sub_path_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T10:19:27.834482+00:00
-- url     : https://prove2.me/submissions/f8094b16-db33-43db-b11e-b08bdc37d0c2

import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_attains_peak
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_rawSup_nonneg
import Mathlib.MeasureTheory.MeasurableSpace.Defs

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
    runningSup X u ω - X.X u ω = 0 := by
  have hraw := (runningSup_eq_rawSup_nonneg X u ω).1
  have hpeak := (firstUpcrossing_attains_peak X b hb ω u hu).2
  have hEq : runningSup X u ω = X.X u ω := by
    rw [hraw]
    simpa only [sSup_image'] using hpeak
  rw [hEq]
  simp
