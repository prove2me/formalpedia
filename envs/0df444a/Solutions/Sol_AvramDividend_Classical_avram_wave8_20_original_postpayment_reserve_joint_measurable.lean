-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_20_original_postpayment_reserve_joint_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T20:15:40.808846+00:00
-- url     : https://prove2.me/submissions/d1270d0d-2e2f-415b-a110-3a4734bc2e1d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_source_postPayment_discounted_exponential_joint_time_path_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Joint measurability of the literal original postpayment reserve. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) :
    Measurable (fun z : ℝ≥0 × Ω =>
      x + X.X z.1 z.2 - rightLimit D z.1 z.2) := by
  have hExp : Measurable (fun z : ℝ≥0 × Ω =>
      Real.exp ((1 : ℝ) *
        (x + X.X z.1 z.2 - rightLimit D z.1 z.2) -
        (z.1 : ℝ) * (0 : ℝ))) :=
    avram_wave4_03_source_postPayment_discounted_exponential_joint_time_path_measurable
      X x D hD 1 0
  have hLog := hExp.log
  simpa only [one_mul, mul_zero, sub_zero, Real.log_exp] using hLog
