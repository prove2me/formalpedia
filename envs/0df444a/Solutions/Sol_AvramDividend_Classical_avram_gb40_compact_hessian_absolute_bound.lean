-- Prove2me | solution 1 for AvramDividend.Classical.avram_gb40_compact_hessian_absolute_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T10:30:03.155305+00:00
-- url     : https://prove2.me/submissions/af84607d-8e26-4992-86b1-b185401715bb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical

/-- A compact interval bounds its continuous Hessian absolutely. -/
theorem solution
    (w : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hc : ContinuousOn (fun y => |iteratedDeriv 2 w y|) (Icc a b)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y ∈ Icc a b, |iteratedDeriv 2 w y| ≤ B := by
  obtain ⟨y, hy, hmax⟩ :=
    isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab) hc
  refine ⟨|iteratedDeriv 2 w y|, abs_nonneg _, ?_⟩
  intro z hz
  exact hmax hz
