-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_physical_first_mark_signed_mesh_obstruction_with_real_noise_values
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T12:27:15.402395+00:00
-- url     : https://prove2.me/submissions/469a4546-dd6d-478c-8997-0bbaa58f237a

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_physical_unitmark_ruin_gap_blocks_vanishing_signed_mesh
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    (y : ℝ) (hy : 0 ≤ y) (hycap : y ≤ 1 / 5)
    (τ : ℝ≥0) (B N : ℝ≥0 → ℝ)
    (hFirst : N τ = 1)
    (hTube : B τ ≤ (1 / 100 : ℝ))
    (hτ : (τ : ℝ) ≤ 1 / 10)
    (Jfull : ℝ)
    (hFull : Jfull = -2 * N τ + 2 * (τ : ℝ))
    (Drift Err : ℕ → ℝ)
    (hDrift : ∀ k, Drift k ≤ 0)
    (hErr : Tendsto Err atTop (nhds (0 : ℝ)))
    (hLedger : ∀ k,
      0 ≤ 1 + y + y ^ 2 + B τ + Jfull + Drift k + Err k) :
    False := by
  have hJ : Jfull = -2 + 2 * (τ : ℝ) := by
    rw [hFull, hFirst]
    ring
  have hLed : ∀ k,
      0 ≤ (1 + y + y ^ 2) + B τ - 2 + 2 * (τ : ℝ) +
        Drift k + Err k := by
    intro k
    have hk := hLedger k
    rw [hJ] at hk
    nlinarith
  exact avram_jump6_A_physical_unitmark_ruin_gap_blocks_vanishing_signed_mesh
    y (B τ) (τ : ℝ) hy hycap hTube hτ Drift Err hDrift hErr hLed
