-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_03_actual_stopped_positive_ruin_dividend_mass_cumulative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T10:54:48.959403+00:00
-- url     : https://prove2.me/submissions/e30f04c9-6575-4408-bad3-d616b3d2c532

import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_paymentTimes_eq_strict_of_pos
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ico_zero_eq_dividendValue

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Full pre-ruin mass of the original controlled dividend Stieltjes measure.
    This includes any diffuse/singular-continuous mass, but not a right atom
    at the finite positive ruin time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (τ : ℝ≥0) (hτ : 0 < τ) :
    dividendMeasure D ω
      (paymentTimes (τ : ℝ≥0∞) ∩ Set.Iic (τ : ℝ)) =
      ENNReal.ofReal (D τ ω) := by
  have hτe : (0 : ℝ≥0∞) < (τ : ℝ≥0∞) := by
    exact_mod_cast hτ
  rw [paymentTimes_eq_strict_of_pos (τ : ℝ≥0∞) hτe]
  have hset :
      {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal t < (τ : ℝ≥0∞)} ∩
          Set.Iic (τ : ℝ) = Set.Ico (0 : ℝ) (τ : ℝ) := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Iic, Set.mem_Ico]
    constructor
    · rintro ⟨⟨ht0, hte⟩, _⟩
      exact ⟨ht0, (ENNReal.ofReal_lt_coe_iff ht0).mp hte⟩
    · rintro ⟨ht0, htτ⟩
      exact ⟨⟨ht0, (ENNReal.ofReal_lt_coe_iff ht0).mpr htτ⟩, le_of_lt htτ⟩
  rw [hset]
  exact dividendMeasure_Ico_zero_eq_dividendValue D hD ω τ
