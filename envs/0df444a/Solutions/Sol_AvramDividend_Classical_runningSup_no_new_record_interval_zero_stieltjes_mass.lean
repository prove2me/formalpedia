-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_no_new_record_interval_zero_stieltjes_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T00:23:12.678702+00:00
-- url     : https://prove2.me/submissions/04c8275a-1835-4f88-8693-4a8451a1adbe

import Definitions.Def_AvramDividend_Classical_Reflection
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_runningSup_const_between_of_path_below_old_record
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_Ioc_eq_record_increment
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

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
  have hConst : runningSup X v ω = runningSup X u ω :=
    runningSup_const_between_of_path_below_old_record
      X ω u v huv hBelow
  rw [runningSup_dividendMeasure_Ioc_eq_record_increment
    X ω (u : ℝ) (v : ℝ)]
  simp only [Real.toNNReal_coe, hConst, sub_self, ENNReal.ofReal_zero]
