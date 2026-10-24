-- Prove2me | solution 1 for AvramDividend.Classical.continuous_test_abs_le_on_finite_cap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T22:50:44.155157+00:00
-- url     : https://prove2.me/submissions/c16b7cf3-226c-441d-b7fb-83f09da5c313

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Topology.Order.Compact

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

/-- A verification test continuous on nonnegative reserves is bounded on a finite cap. -/
theorem solution
    (w : ℝ → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hw : ContinuousOn w (Ici 0)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y : ℝ, 0 ≤ y → y ≤ B → |w y| ≤ M := by
  have hSub : Icc (0 : ℝ) B ⊆ Ici 0 := by
    intro y hy
    exact hy.1
  have hAbs : ContinuousOn (fun y : ℝ => |w y|) (Icc (0 : ℝ) B) :=
    (hw.mono hSub).abs
  have hNonempty : (Icc (0 : ℝ) B).Nonempty := by
    exact ⟨0, ⟨le_refl _, hB⟩⟩
  obtain ⟨a, ha, hmax⟩ :=
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) B)).exists_isMaxOn
      hNonempty hAbs
  refine ⟨|w a|, abs_nonneg _, ?_⟩
  intro y hy0 hyB
  exact hmax ⟨hy0, hyB⟩
