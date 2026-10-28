-- Prove2me | solution 2 for AvramDividend.Classical.usc_compact_prefix_hit_iff_sup_ge
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T21:12:58.752492+00:00
-- url     : https://prove2.me/submissions/2184debd-5ed7-4ce5-bad2-019c94247060

import Mathlib

open Set Topology
open scoped NNReal

theorem solution
    (R : ℝ≥0 → ℝ) (t : ℝ≥0) (x : ℝ)
    (husc : UpperSemicontinuousOn R (Icc 0 t)) :
    (∃ s : ℝ≥0, s ≤ t ∧ x ≤ R s) ↔
      x ≤ sSup (R '' Icc (0 : ℝ≥0) t) := by
  obtain ⟨s0, hs0, hmax⟩ := UpperSemicontinuousOn.exists_isMaxOn
    (⟨0, left_mem_Icc.mpr (by simp)⟩ : (Icc (0 : ℝ≥0) t).Nonempty) isCompact_Icc husc
  have hbdd : BddAbove (R '' Icc (0 : ℝ≥0) t) := ⟨R s0, by
    rintro _ ⟨s, hs, rfl⟩; exact hmax hs⟩
  constructor
  · rintro ⟨s, hst, hx⟩
    exact hx.trans (le_csSup hbdd ⟨s, ⟨by simp, hst⟩, rfl⟩)
  · intro hx
    refine ⟨s0, hs0.2, hx.trans (csSup_le ⟨R s0, s0, hs0, rfl⟩ ?_)⟩
    rintro _ ⟨s, hs, rfl⟩; exact hmax hs
