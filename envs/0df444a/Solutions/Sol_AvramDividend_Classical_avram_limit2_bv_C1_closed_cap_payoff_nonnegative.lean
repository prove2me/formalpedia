-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_bv_C1_closed_cap_payoff_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T20:10:33.395777+00:00
-- url     : https://prove2.me/submissions/de5548bb-6c49-4a4f-a473-68718284f917

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_positive_cap_C1_closed_endpoint_two_point_jump_envelope
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- C1 gradient bounds imply nonnegative original BV payoff at all capped
    nonnegative reserves, including the closed cap and infinite cap. -/
theorem solution
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw0 : 0 ≤ w 0)
    (hwCont : ContinuousOn w (Ici (0 : ℝ)))
    (hwSmooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hwGrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y) :
    ∀ y : ℝ, 0 ≤ y → ENNReal.ofReal y ≤ C → 0 ≤ w y := by
  intro y hy hyC
  have hSec :=
    avram_wave7_02_original_positive_cap_C1_closed_endpoint_two_point_jump_envelope
      C hC w hwCont hwSmooth hwGrad y hy hyC
  have hAt := hSec 0 ⟨le_rfl, hy⟩ y ⟨hy, le_rfl⟩ hy
  linarith only [hAt, hw0, hy]
