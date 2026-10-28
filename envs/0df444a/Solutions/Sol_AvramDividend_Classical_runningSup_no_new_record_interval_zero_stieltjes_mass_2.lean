-- Prove2me | solution 2 for AvramDividend.Classical.runningSup_no_new_record_interval_zero_stieltjes_mass
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T00:23:49.553838+00:00
-- url     : https://prove2.me/submissions/a089de98-edbe-4dad-b525-17c36880ff02

import Definitions.Def_AvramDividend_Classical_Reflection
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_runningSup_const_between_of_path_below_old_record
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_Ioc_eq_record_increment
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.ENNReal.Basic

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (u v : ℝ≥0) (huv : u ≤ v)
    (hBelow : ∀ t : ℝ≥0, u ≤ t → t ≤ v →
      X.X t ω ≤ runningSup X u ω) :
    (dividendMeasure (runningSup X) ω)
      (Set.Ioc (u : ℝ) (v : ℝ)) = 0 := by
  rw [runningSup_dividendMeasure_Ioc_eq_record_increment, Real.toNNReal_coe, Real.toNNReal_coe,
    runningSup_const_between_of_path_below_old_record X ω u v huv hBelow, sub_self,
    ENNReal.ofReal_zero]
