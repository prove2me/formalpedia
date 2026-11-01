-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_03_positive_ruin_finite_horizon_payment_region_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T11:16:54.463057+00:00
-- url     : https://prove2.me/submissions/db6c74dc-6a1f-43ba-888c-5a2ddfd19526

import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_paymentTimes_eq_strict_of_pos

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Original payment-time region: a closed cutoff before ruin, but no
    payment atom at a positive finite ruin time. Rewrites every Stieltjes
    reward weight without erasing diffuse or singular-continuous payments. -/
theorem solution
    (τ T : ℝ≥0) (hτ : 0 < τ) :
    paymentTimes (τ : ℝ≥0∞) ∩ Set.Iic (T : ℝ) =
      if T < τ then Set.Icc (0 : ℝ) (T : ℝ)
      else Set.Ico (0 : ℝ) (τ : ℝ) := by
  have hτe : (0 : ℝ≥0∞) < (τ : ℝ≥0∞) := by
    exact_mod_cast hτ
  rw [paymentTimes_eq_strict_of_pos (τ : ℝ≥0∞) hτe]
  split_ifs with hT
  · ext t
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Iic, Set.mem_Icc]
    constructor
    · rintro ⟨⟨ht0, _⟩, htT⟩
      exact ⟨ht0, htT⟩
    · rintro ⟨ht0, htT⟩
      refine ⟨⟨ht0, ?_⟩, htT⟩
      exact (ENNReal.ofReal_lt_coe_iff ht0).mpr
        (lt_of_le_of_lt htT hT)
  · have hτT : τ ≤ T := le_of_not_gt hT
    ext t
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Iic, Set.mem_Ico]
    constructor
    · rintro ⟨⟨ht0, hte⟩, _⟩
      exact ⟨ht0, (ENNReal.ofReal_lt_coe_iff ht0).mp hte⟩
    · rintro ⟨ht0, htτ⟩
      refine ⟨⟨ht0, (ENNReal.ofReal_lt_coe_iff ht0).mpr htτ⟩, ?_⟩
      exact le_trans (le_of_lt htτ) hτT
