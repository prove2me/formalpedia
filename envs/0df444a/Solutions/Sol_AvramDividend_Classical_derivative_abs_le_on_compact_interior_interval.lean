-- Prove2me | solution 1 for AvramDividend.Classical.derivative_abs_le_on_compact_interior_interval
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T23:00:57.817959+00:00
-- url     : https://prove2.me/submissions/9cbb8c7d-a3f5-4157-85dd-2c1cf08ee640

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Topology.Order.Compact

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

/-- A C1 verification function has uniformly bounded derivative on compact interior intervals. -/
theorem solution
    (w : ℝ → ℝ) (a b u v : ℝ)
    (hw : ContDiffOn ℝ 1 w (Ioo a b))
    (hau : a < u) (huv : u ≤ v) (hvb : v < b) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ y : ℝ, u ≤ y → y ≤ v → |deriv w y| ≤ M := by
  have hSub : Icc u v ⊆ Ioo a b := by
    intro y hy
    exact ⟨lt_of_lt_of_le hau hy.1, lt_of_le_of_lt hy.2 hvb⟩
  have hDeriv : ContinuousOn (deriv w) (Ioo a b) :=
    hw.continuousOn_deriv_of_isOpen isOpen_Ioo (le_refl 1)
  have hAbs : ContinuousOn (fun y : ℝ => |deriv w y|) (Icc u v) :=
    (hDeriv.mono hSub).abs
  have hNonempty : (Icc u v).Nonempty :=
    ⟨u, ⟨le_refl _, huv⟩⟩
  obtain ⟨z, hz, hmax⟩ :=
    (isCompact_Icc : IsCompact (Icc u v)).exists_isMaxOn hNonempty hAbs
  refine ⟨|deriv w z|, abs_nonneg _, ?_⟩
  intro y hyu hyv
  exact hmax ⟨hyu, hyv⟩
