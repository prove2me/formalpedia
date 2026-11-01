-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_03_positive_ruin_closed_horizon_stopped_dividend_mass_piecewise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T11:01:38.496271+00:00
-- url     : https://prove2.me/submissions/27b94cb3-ddb5-475d-ab84-8f069798d197

import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_paymentTimes_eq_strict_of_pos
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ico_zero_eq_dividendValue
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The two mutually exclusive chronological endpoint conventions of the
    actual stopped full Stieltjes dividend measure. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (τ T : ℝ≥0) (hτ : 0 < τ) :
    dividendMeasure D ω
      (paymentTimes (τ : ℝ≥0∞) ∩ Set.Iic (T : ℝ)) =
      if T < τ then ENNReal.ofReal (rightLimit D T ω)
      else ENNReal.ofReal (D τ ω) := by
  have hτe : (0 : ℝ≥0∞) < (τ : ℝ≥0∞) := by
    exact_mod_cast hτ
  rw [paymentTimes_eq_strict_of_pos (τ : ℝ≥0∞) hτe]
  split_ifs with hT
  · have hset :
        {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal t < (τ : ℝ≥0∞)} ∩
            Set.Iic (T : ℝ) = Set.Icc (0 : ℝ) (T : ℝ) := by
      ext t
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Iic, Set.mem_Icc]
      constructor
      · rintro ⟨⟨ht0, _⟩, htT⟩
        exact ⟨ht0, htT⟩
      · rintro ⟨ht0, htT⟩
        refine ⟨⟨ht0, ?_⟩, htT⟩
        exact (ENNReal.ofReal_lt_coe_iff ht0).mpr
          (lt_of_le_of_lt htT hT)
    rw [hset]
    exact avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit D hD ω T
  · have hτT : τ ≤ T := le_of_not_gt hT
    have hset :
        {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal t < (τ : ℝ≥0∞)} ∩
            Set.Iic (T : ℝ) = Set.Ico (0 : ℝ) (τ : ℝ) := by
      ext t
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Iic, Set.mem_Ico]
      constructor
      · rintro ⟨⟨ht0, hte⟩, _⟩
        exact ⟨ht0, (ENNReal.ofReal_lt_coe_iff ht0).mp hte⟩
      · rintro ⟨ht0, htτ⟩
        refine ⟨⟨ht0, (ENNReal.ofReal_lt_coe_iff ht0).mpr htτ⟩, ?_⟩
        exact le_trans (le_of_lt htτ) hτT
    rw [hset]
    exact dividendMeasure_Ico_zero_eq_dividendValue D hD ω τ
