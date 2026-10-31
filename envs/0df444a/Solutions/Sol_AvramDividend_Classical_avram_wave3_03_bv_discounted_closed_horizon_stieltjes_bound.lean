-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_03_bv_discounted_closed_horizon_stieltjes_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T07:57:37.114983+00:00
-- url     : https://prove2.me/submissions/80897763-74bc-465d-9293-c3bf2ebbc0db

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_discounted_stieltjes_lintegral_le_measure
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (q : ℝ) (hq : 0 ≤ q)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) :
    (∫⁻ t in Icc (0 : ℝ) (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
        ENNReal.ofReal (rightLimit D T ω) := by
  calc
    _ ≤ dividendMeasure D ω (Icc (0 : ℝ) (T : ℝ)) :=
      discounted_stieltjes_lintegral_le_measure q hq
        (dividendMeasure D ω) (Icc (0 : ℝ) (T : ℝ))
        measurableSet_Icc (by intro t ht; exact ht.1)
    _ = _ := avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit D hD ω T
