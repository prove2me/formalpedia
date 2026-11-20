-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_first_exit_scale_cross_inequality_to_domination
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T21:04:43.943187+00:00
-- url     : https://prove2.me/submissions/6ce30bd4-b3a2-4453-9ff9-d173105e21a8

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Basic
set_option autoImplicit false
open MeasureTheory Set Topology
noncomputable section

theorem solution
    (w W : ℝ → ℝ)
    (hw1 : 0 ≤ w 1) (hW1 : 0 < W 1)
    (hExit : ∀ y : ℝ, 1 ≤ y →
      w y * W 1 ≤ w 1 * W y) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ y : ℝ, 1 ≤ y → w y ≤ A * W y := by
  let A : ℝ := w 1 / W 1
  have hA : 0 ≤ A := div_nonneg hw1 hW1.le
  refine ⟨A, hA, ?_⟩
  intro y hy
  calc
    w y ≤ (w 1 * W y) / W 1 :=
      (le_div_iff₀ hW1).2 (hExit y hy)
    _ = A * W y := by dsimp [A]; ring
