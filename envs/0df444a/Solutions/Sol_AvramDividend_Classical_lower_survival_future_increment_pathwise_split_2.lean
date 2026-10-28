-- Prove2me | solution 2 for AvramDividend.Classical.lower_survival_future_increment_pathwise_split
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:04:51.480058+00:00
-- url     : https://prove2.me/submissions/33e58832-f425-40f0-8873-5d31f2775b54

import Mathlib.Data.NNReal.Basic
import Theorems.Thm_AvramDividend_Classical_lower_survival_closed_horizon_pathwise_split
import Theorems.Thm_AvramDividend_Classical_lower_survival_shifted_interval_reparam

open Set
open scoped NNReal
open AvramDividend.Classical
theorem solution
    {Ω : Type*} (Y : ℝ≥0 → Ω → ℝ) (x : ℝ) (s u : ℝ≥0) :
    {ω : Ω | ∀ v : ℝ≥0, v ≤ s + u → 0 ≤ x + Y v ω} =
      {ω : Ω | ∀ v : ℝ≥0, v ≤ s → 0 ≤ x + Y v ω} ∩
      {ω : Ω | ∀ v : ℝ≥0, v ≤ u →
        0 ≤ (x + Y s ω) + (Y (s + v) ω - Y s ω)} := by 
  rw [lower_survival_closed_horizon_pathwise_split Y x s (s + u) le_self_add]
  ext ω
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
  rw [lower_survival_shifted_interval_reparam (fun v => Y v ω) x s u]
