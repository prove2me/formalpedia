-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB95_product_refinement_endpoint_equalities
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T20:01:16.827953+00:00
-- url     : https://prove2.me/submissions/98cf647d-4e5c-44f8-8bd3-8df264484fe7

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

/-- Endpoints agree between the original coarse grid and its product refinement. -/
theorem solution
    (n m b i : ℕ) (hn : 0 < n) (hb : 0 < b) :
    let D : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
    let δ : ℝ := (n : ℝ) / (((m + 1) * b : ℕ) : ℝ)
    ((((i : ℝ≥0) * D) : ℝ) = ((i * b : ℕ) : ℝ) * δ) ∧
    (((((i : ℝ≥0) * D) + D : ℝ≥0) : ℝ) =
      ((i * b + b : ℕ) : ℝ) * δ) := by
  intro D δ
  have hm : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hb
  have hD : (D : ℝ) = (b : ℝ) * δ := by
    dsimp [D, δ]
    simp only [NNReal.coe_div, NNReal.coe_natCast, Nat.cast_mul]
    field_simp
    all_goals ring
  constructor
  · simp only [NNReal.coe_mul, NNReal.coe_natCast, hD]
    push_cast
    all_goals ring
  · simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_natCast, hD]
    push_cast
    all_goals ring