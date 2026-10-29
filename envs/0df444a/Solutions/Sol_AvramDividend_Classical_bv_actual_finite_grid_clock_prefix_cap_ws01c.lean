-- Prove2me | solution 1 for AvramDividend.Classical.bv_actual_finite_grid_clock_prefix_cap_ws01c
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T00:05:04.953739+00:00
-- url     : https://prove2.me/submissions/b08f261e-e407-4a42-b3e1-d873c456da29

import Mathlib
import Definitions.Def_AvramDividend_Classical_BvFiniteGridClocks_ws01c
import Theorems.Thm_AvramDividend_Classical_bv_finite_fold_to_prefix_capped_clock_ws01c
import Theorems.Thm_AvramDividend_Classical_bv_finite_grid_NNReal_coe_ws01c

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} (Y : ℝ≥0 → Ω → ℝ)
    (ω : Ω) (lower : ℝ) (h T H : ℝ≥0) (M : ℕ)
    (hTH : T ≤ H) :
    (((bv_finite_grid_below_NNReal_ws01c
      Y lower H
        ((List.range (M + 1)).map
          (fun k : ℕ => (k : ℝ≥0) * h)) ω : ℝ≥0) : ℝ≥0∞) ⊓
      (T : ℝ≥0∞)) =
    ((⨅ (k : ℕ) (_ : k ≤ M),
        if Y ((k : ℝ≥0) * h) ω < lower then
          (((k : ℝ≥0) * h) : ℝ≥0∞) else ⊤) ⊓
        (T : ℝ≥0∞)) := by
  have key : ∀ L : List ℝ≥0,
      ((L.foldr (fun t u => (if Y t ω < lower then t else H) ⊓ u) H : ℝ≥0) : ℝ≥0∞) =
      L.foldr (fun t u => (if Y t ω < lower then (t : ℝ≥0∞) else (H : ℝ≥0∞)) ⊓ u) (H : ℝ≥0∞) := by
    intro L
    induction L with
    | nil => rfl
    | cons a L ih =>
      simp only [List.foldr_cons]
      rw [ENNReal.coe_min, ih]
      congr 1
      split_ifs <;> rfl
  have e := key ((List.range (M + 1)).map (fun k : ℕ => (k : ℝ≥0) * h))
  unfold AvramDividend.Classical.bv_finite_grid_below_NNReal_ws01c
  rw [e, List.foldr_map]
  exact AvramDividend.Classical.bv_finite_fold_to_prefix_capped_clock_ws01c M
    (fun k => (((k : ℝ≥0) * h : ℝ≥0) : ℝ≥0∞)) (fun k => Y ((k : ℝ≥0) * h) ω < lower)
    (H : ℝ≥0∞) (T : ℝ≥0∞) (by exact_mod_cast hTH)
