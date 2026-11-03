-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_08_zero_clock_paymentTimes_sub_source_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T15:07:06.041191+00:00
-- url     : https://prove2.me/submissions/f220b864-2658-4aa2-afcc-ebe70bbe71e0

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Set AvramDividend.Classical
open scoped NNReal ENNReal
theorem solution
    (σ : ℝ≥0∞) (T : ℝ) :
    paymentTimes (min σ (0 : ℝ≥0∞)) ∩ Iic T ⊆
      paymentTimes σ ∩ Iic (0 : ℝ) := by
  intro t ht
  have hmem := ht.1
  change 0 ≤ t ∧ (t = 0 ∨ ENNReal.ofReal t < min σ (0 : ℝ≥0∞)) at hmem
  have hz : t = 0 := by
    rcases hmem.2 with heq | hlt
    · exact heq
    · have hb : ENNReal.ofReal t < (0 : ℝ≥0∞) :=
        lt_of_lt_of_le hlt (min_le_right σ (0 : ℝ≥0∞))
      have hle : (0 : ℝ≥0∞) ≤ ENNReal.ofReal t := bot_le
      exact (lt_irrefl (0 : ℝ≥0∞) (lt_of_le_of_lt hle hb)).elim
  subst t
  constructor
  · change 0 ≤ (0 : ℝ) ∧ ((0 : ℝ) = 0 ∨ ENNReal.ofReal 0 < σ)
    exact ⟨le_rfl, Or.inl rfl⟩
  · change (0 : ℝ) ≤ 0
    exact le_rfl
