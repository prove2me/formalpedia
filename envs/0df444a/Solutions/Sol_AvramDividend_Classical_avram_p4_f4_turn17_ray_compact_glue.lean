-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f4_turn17_ray_compact_glue
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T12:23:33.794647+00:00
-- url     : https://prove2.me/submissions/984f4207-c21e-4b3b-a89d-741e67e1d016

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (r : ℝ) (hr : 0 ≤ r) (w : ℝ → ℝ)
    (hw_neg : ∀ y < 0, w y = 0)
    (K M : ℝ) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hRay : ∀ y : ℝ, 1 ≤ y → w y ≤ K * Real.exp (r * y))
    (hCompact : ∀ y : ℝ, 0 ≤ y → y ≤ 1 → w y ≤ M) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ y : ℝ,
      w y ≤ L * Real.exp (r * y) := by
  let L : ℝ := max K M
  have hL : 0 ≤ L := le_trans hK (le_max_left K M)
  refine ⟨L, hL, ?_⟩
  intro y
  by_cases hyNeg : y < 0
  · rw [hw_neg y hyNeg]
    exact mul_nonneg hL (le_of_lt (Real.exp_pos _))
  by_cases hyRay : 1 ≤ y
  · have hCmp := mul_le_mul_of_nonneg_right
        (le_max_left K M) (le_of_lt (Real.exp_pos (r * y)))
    exact (hRay y hyRay).trans (by simpa [L] using hCmp)
  · have hy0 : 0 ≤ y := le_of_not_gt hyNeg
    have hy1 : y ≤ 1 := le_of_lt (lt_of_not_ge hyRay)
    have hExp : 1 ≤ Real.exp (r * y) := by
      have hry : 0 ≤ r * y := mul_nonneg hr hy0
      nlinarith [Real.add_one_le_exp (r * y)]
    have hCmp := mul_le_mul_of_nonneg_left hExp hL
    calc
      w y ≤ M := hCompact y hy0 hy1
      _ ≤ L := le_max_right K M
      _ = L * 1 := by ring
      _ ≤ L * Real.exp (r * y) := by simpa using hCmp
