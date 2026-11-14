-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_a22_original_C1_negative_jump_candidate_loss_uniform_zero_band_bound_without_zero_boundary_value
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T10:55:58.13325+00:00
-- url     : https://prove2.me/submissions/2f65490f-1ffd-4271-a022-accc55aa270a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical Set Filter AvramDividend.Classical
open scoped Topology
noncomputable section

theorem solution
    (w : ℝ → ℝ)
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw0 : 0 ≤ w 0)
    (ε : ℝ) (hε : 0 < ε)
    (hmono : MonotoneOn w (Icc (0 : ℝ) ε)) :
    ∀ y ∈ Ioc (0 : ℝ) ε, ∀ z : ℝ, z < 0 →
      0 ≤ w y - w (y + z) ∧ w y - w (y + z) ≤ w ε := by
  intro y hy z hz
  have hzero : (0 : ℝ) ∈ Icc 0 ε := ⟨le_rfl, le_of_lt hε⟩
  have hyband : y ∈ Icc (0 : ℝ) ε := ⟨le_of_lt hy.1, hy.2⟩
  have hy_nonneg : 0 ≤ w y :=
    hw0.trans (hmono hzero hyband (le_of_lt hy.1))
  have hy_le : w y ≤ w ε :=
    hmono hyband ⟨le_of_lt hε, le_rfl⟩ hy.2
  by_cases hcross : y + z < 0
  · rw [hw_neg (y + z) hcross]
    constructor
    · simpa using hy_nonneg
    · simpa using hy_le
  · have hpost0 : 0 ≤ y + z := le_of_not_gt hcross
    have hposty : y + z ≤ y := by linarith
    have hpost : y + z ∈ Icc (0 : ℝ) ε :=
      ⟨hpost0, hposty.trans hy.2⟩
    have hpost_nonneg : 0 ≤ w (y + z) :=
      hw0.trans (hmono hzero hpost hpost0)
    have hpost_le : w (y + z) ≤ w y :=
      hmono hpost hyband hposty
    constructor <;> linarith
