-- Prove2me | solution 1 for AvramDividend.Classical.barrierFuturePaymentTimes_translate_iff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T21:13:33.268654+00:00
-- url     : https://prove2.me/submissions/a51de757-8310-4614-a492-6ecbf3c70d10

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    (u : ℝ≥0) (σ : ℝ≥0∞) (t : ℝ) (ht : 0 < t) :
    t ∈ paymentTimes σ ↔
      (u : ℝ) + t ∈ paymentTimes ((u : ℝ≥0∞) + σ) := by
  have hu : (0 : ℝ) ≤ u := u.2
  simp only [paymentTimes, mem_setOf_eq]
  rw [ENNReal.ofReal_add hu ht.le, ENNReal.ofReal_coe_nnreal,
    ENNReal.add_lt_add_iff_left ENNReal.coe_ne_top]
  constructor
  · rintro ⟨-, h | h⟩
    · exact absurd h ht.ne'
    · exact ⟨by linarith, Or.inr h⟩
  · rintro ⟨-, h | h⟩
    · linarith
    · exact ⟨ht.le, Or.inr h⟩
