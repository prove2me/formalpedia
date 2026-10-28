-- Prove2me | solution 1 for AvramDividend.Classical.paymentTimes_translated_iff_shifted_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:21:57.086798+00:00
-- url     : https://prove2.me/submissions/78965b40-179a-4a33-8149-0b74dc96c125

import Mathlib.Data.ENNReal.Real
import Mathlib.Data.NNReal.Basic
import Mathlib.Tactic.Positivity
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (u : ℝ≥0) (ρ : ℝ≥0∞) (t : ℝ) (ht : 0 < t) :
    (u : ℝ) + t ∈ paymentTimes ((u : ℝ≥0∞) + ρ) ↔
      t ∈ paymentTimes ρ := by
  have hu : (0:ℝ) ≤ u := u.2
  simp only [paymentTimes, Set.mem_setOf_eq]
  have e : ENNReal.ofReal ((u : ℝ) + t) = (u : ℝ≥0∞) + ENNReal.ofReal t := by
    rw [ENNReal.ofReal_add hu ht.le, ENNReal.ofReal_coe_nnreal]
  rw [e, ENNReal.add_lt_add_iff_left ENNReal.coe_ne_top]
  constructor
  · rintro ⟨-, h | h⟩
    · linarith
    · exact ⟨ht.le, Or.inr h⟩
  · rintro ⟨-, h | h⟩
    · linarith
    · exact ⟨by linarith, Or.inr h⟩
