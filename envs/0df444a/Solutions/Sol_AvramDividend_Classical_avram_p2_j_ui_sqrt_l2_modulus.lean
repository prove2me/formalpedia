-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_sqrt_l2_modulus
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T17:37:56.570858+00:00
-- url     : https://prove2.me/submissions/09610542-0100-4622-b981-c74c9aabe7e7

import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Positivity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal ENNReal

/-! An explicit square-root modulus for a finite L² envelope. -/
theorem solution (B : ℝ≥0) (ε : ENNReal) (hε : 0 < ε) :
    ∃ δ : ENNReal, 0 < δ ∧
      (B : ENNReal) * δ ^ (1 / 2 : ℝ) ≤ ε := by
  obtain ⟨c, hc, hmul⟩ :=
    ENNReal.exists_nnreal_pos_mul_lt
      (a := (B : ENNReal)) (b := ε) (by simp) (ne_of_gt hε)
  have hpow : ((c : ENNReal) ^ 2) ^ (1 / 2 : ℝ) = (c : ENNReal) := by
    simpa [ENNReal.rpow_two] using
      (ENNReal.rpow_mul (c : ENNReal) 2 (1 / 2 : ℝ)).symm
  refine ⟨(c : ENNReal) ^ 2, by positivity, ?_⟩
  rw [hpow, mul_comm]
  exact le_of_lt hmul
