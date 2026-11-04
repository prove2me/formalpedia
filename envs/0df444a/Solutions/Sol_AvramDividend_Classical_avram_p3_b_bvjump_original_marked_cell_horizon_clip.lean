-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_original_marked_cell_horizon_clip
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:48:14.21146+00:00
-- url     : https://prove2.me/submissions/de155268-a513-47b3-88f4-29e0ddc5bdc9

import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Tauto
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_source_interval_horizon_clip
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (Ω : Type*) (s t T : ℝ≥0) (A : Set Ω) (B : Set ℝ) :
    (((Ioc s t ×ˢ A) ×ˢ B) ∩
      {p : ((ℝ≥0 × Ω) × ℝ) | p.1.1 ≤ T}) =
    ((Ioc s (min t T) ×ˢ A) ×ˢ B) := by
  ext p
  rcases p with ⟨⟨u, ω⟩, z⟩
  simp only [mem_inter_iff, mem_setOf_eq, mem_prod, mem_Ioc, le_min_iff]
  tauto
