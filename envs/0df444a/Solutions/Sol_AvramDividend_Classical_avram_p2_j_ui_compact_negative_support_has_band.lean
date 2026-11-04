-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_compact_negative_support_has_band
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:56:01.119331+00:00
-- url     : https://prove2.me/submissions/57a78d85-8f1e-4596-bca4-e0980da5678b

import Mathlib.Data.Real.Basic
import Mathlib.Topology.UniformSpace.Real
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

/-- Compact topological support strictly below zero has a negative support gap. -/
theorem solution (g : ℝ → ℝ)
    (hc : IsCompact (tsupport g))
    (hneg : tsupport g ⊆ Iio (0 : ℝ)) :
    ∃ a ε : ℝ, 0 < ε ∧
      (∀ y : ℝ, y < a → g y = 0) ∧
      (∀ y : ℝ, -ε < y → g y = 0) := by
  by_cases hnonempty : (tsupport g).Nonempty
  · obtain ⟨a, ha⟩ := hc.bddBelow
    obtain ⟨b, hb, hmax⟩ :=
      hc.exists_isMaxOn hnonempty (continuous_id.continuousOn)
    have hb0 : b < 0 := hneg hb
    refine ⟨a, -b, neg_pos.mpr hb0, ?_, ?_⟩
    · intro y hy
      by_contra hgy
      have hymem : y ∈ tsupport g := subset_tsupport g hgy
      exact (not_lt_of_ge (ha hymem)) hy
    · intro y hy
      by_contra hgy
      have hymem : y ∈ tsupport g := subset_tsupport g hgy
      have hle : y ≤ b := (isMaxOn_iff.mp hmax) y hymem
      linarith
  · have hzero (y : ℝ) : g y = 0 := by
      by_contra hgy
      exact hnonempty ⟨y, subset_tsupport g hgy⟩
    refine ⟨0, 1, by norm_num, ?_, ?_⟩
    · intro y _
      exact hzero y
    · intro y _
      exact hzero y
