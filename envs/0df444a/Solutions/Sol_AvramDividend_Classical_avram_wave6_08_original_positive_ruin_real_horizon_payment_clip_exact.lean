-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_08_original_positive_ruin_real_horizon_payment_clip_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T09:13:25.688355+00:00
-- url     : https://prove2.me/submissions/2f175cf0-e220-47b7-9932-b8b8b02a1a00

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_eq_strict_of_pos

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The genuine finite-horizon payment domain includes a pre-ruin horizon
right payment but excludes a positive ruin-time right payment. -/
theorem solution
    (τ : ℝ≥0) (hτ : 0 < τ) (T : ℝ) (hT : 0 ≤ T) :
    paymentTimes (τ : ℝ≥0∞) ∩ Iic T =
      if T < (τ : ℝ) then Icc 0 T else Ico 0 (τ : ℝ) := by
  have hτE : (0 : ℝ≥0∞) < (τ : ℝ≥0∞) := by exact_mod_cast hτ
  have hpt : paymentTimes (τ : ℝ≥0∞) = Ico 0 (τ : ℝ) := by
    rw [paymentTimes_eq_strict_of_pos (τ : ℝ≥0∞) hτE]
    ext t
    simp only [mem_setOf_eq, mem_Ico]
    constructor
    · rintro ⟨ht0, htE⟩
      exact ⟨ht0, (ENNReal.ofReal_lt_coe_iff ht0).mp htE⟩
    · rintro ⟨ht0, htτ⟩
      exact ⟨ht0, (ENNReal.ofReal_lt_coe_iff ht0).mpr htτ⟩
  rw [hpt]
  split_ifs with hTτ
  · ext t
    simp only [mem_inter_iff, mem_Ico, mem_Iic, mem_Icc]
    constructor
    · rintro ⟨⟨ht0, _⟩, htT⟩
      exact ⟨ht0, htT⟩
    · rintro ⟨ht0, htT⟩
      exact ⟨⟨ht0, lt_of_le_of_lt htT hTτ⟩, htT⟩
  · ext t
    simp only [mem_inter_iff, mem_Ico, mem_Iic]
    constructor
    · exact And.left
    · intro h
      exact ⟨h, le_trans (le_of_lt h.2) (le_of_not_gt hTτ)⟩
