-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_dividendMeasure_zero_until_firstUpcrossing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T17:02:32.172456+00:00
-- url     : https://prove2.me/submissions/ddd312c8-53aa-4082-a1de-7bb9863c0e3e

import Mathlib.Data.NNReal.Defs
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ioc_eq_path_increment_of_mono_rightLim
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_monotone_of_le
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_right_continuous_of_le
import Theorems.Thm_AvramDividend_Classical_rightLim_comp_toNNReal_of_rightContinuous
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_zero_at_firstUpcrossing
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_isDividendStrategy_nonnegative_barrier
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- There is no positive-time Stieltjes dividend mass through the first finite upcrossing. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞))) :
    (dividendMeasure (barrierStrategy X x a) ω)
      (Set.Ioc (0 : ℝ) (u : ℝ)) = 0 := by
  have hto : Monotone (fun r : ℝ => r.toNNReal) := by
    intro s t hst
    exact Real.toNNReal_mono hst
  have hmD : Monotone
      (fun r : ℝ => barrierStrategy X x a r.toNNReal ω) :=
    (barrierStrategy_monotone_of_le X x a hxa ω).comp hto
  have hrD : ∀ r : ℝ,
      Function.rightLim
        (fun v : ℝ => barrierStrategy X x a v.toNNReal ω) r =
      barrierStrategy X x a r.toNNReal ω := by
    intro r
    exact rightLim_comp_toNNReal_of_rightContinuous
      (fun v : ℝ≥0 => barrierStrategy X x a v ω)
      (barrierStrategy_right_continuous_of_le X x a hxa ω) r
  have hzero0 : barrierStrategy X x a 0 ω = 0 :=
    (barrierStrategy_isDividendStrategy_nonnegative_barrier
      X x a hx0 (le_trans hx0 hxa)).1 ω
  have hzeroU : barrierStrategy X x a u ω = 0 :=
    barrierStrategy_zero_at_firstUpcrossing X x a hxa ω u hu
  have hm :=
    dividendMeasure_Ioc_eq_path_increment_of_mono_rightLim
      (barrierStrategy X x a) ω 0 (u : ℝ) hmD hrD
  simpa only [Real.toNNReal_zero, Real.toNNReal_coe,
    hzero0, hzeroU, sub_self, ENNReal.ofReal_zero] using hm
