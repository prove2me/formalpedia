-- Prove2me | solution 1 for BookProof.WeakSecondDeriv.exists_unitTest
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T17:20:54.597927+00:00
-- url     : https://prove2.me/submissions/080e47ce-b2d0-422b-b0f5-5e88e1913a34

-- Generated from ChapterWeakSecondDerivative.lean — solution of BookProof.WeakSecondDeriv.exists_unitTest
import Mathlib
import Definitions.Def_ChapterWeakSecondDerivative
open BookProof.WeakSecondDeriv




open MeasureTheory Filter Topology intervalIntegral Set

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution : ∃ ρ : ℝ → ℝ, IsTestFun ρ ∧ ∫ x, ρ x = 1 := by

  let f : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  exact ⟨f.normed volume, ⟨f.contDiff_normed, f.hasCompactSupport_normed⟩, f.integral_normed⟩
