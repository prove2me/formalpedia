-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger63_compact_continuous_value_finite_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T00:38:53.32421+00:00
-- url     : https://prove2.me/submissions/be789459-aa0e-4906-806d-664e2a49879c

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
noncomputable section

/-- A continuous interior value function has a finite one-sided lower bound
    on each closed positive-reserve localisation band. -/
theorem solution (a b : ℝ) (hab : a ≤ b) (w : ℝ → ℝ)
    (hw : ContinuousOn w (Icc a b)) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ y : ℝ, a ≤ y → y ≤ b → -B ≤ w y := by
  have hc : IsCompact (w '' Icc a b) :=
    isCompact_Icc.image_of_continuousOn hw
  obtain ⟨L, hL⟩ := hc.isBounded.bddBelow
  let B : ℝ := max 0 (-L)
  refine ⟨B, le_max_left _ _, ?_⟩
  intro y hay hyb
  have hly : L ≤ w y := hL ⟨y, ⟨hay, hyb⟩, rfl⟩
  have hBl : -B ≤ L := by
    have hh : -L ≤ B := le_max_right _ _
    linarith
  exact hBl.trans hly
