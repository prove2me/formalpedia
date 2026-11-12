-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys88_original_closed_cap_negative_mark_value_increment_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T08:22:56.030798+00:00
-- url     : https://prove2.me/submissions/b0ba8da8-27c1-4ea8-a827-0e752a70e412

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_positive_cap_C1_closed_endpoint_two_point_jump_envelope

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped NNReal ENNReal
noncomputable section

/-- An original spectrally negative mark cannot increase a candidate value
on the nonnegative closed cap, including the overshoot below zero. -/
theorem solution
    (C : ℝ≥0∞) (hC : 0 < C)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (b z : ℝ) (hb : 0 ≤ b) (hbC : ENNReal.ofReal b ≤ C)
    (hz : z < 0) :
    w (b + z) - w b ≤ 0 := by
  have henv :=
    AvramDividend.Classical.avram_wave7_02_original_positive_cap_C1_closed_endpoint_two_point_jump_envelope
      C hC w hw_cont hw_smooth hw_grad b hb hbC
  have hbmem : b ∈ Icc (0 : ℝ) b := ⟨hb, le_rfl⟩
  have hw0b : 0 ≤ w b := by
    have h := henv 0 ⟨le_rfl, hb⟩ b hbmem hb
    linarith
  by_cases hnonneg : 0 ≤ b + z
  · have hle : b + z ≤ b := by linarith
    have h := henv (b + z) ⟨hnonneg, hle⟩ b hbmem hle
    linarith
  · have hbelow : b + z < 0 := lt_of_not_ge hnonneg
    rw [hw_neg (b + z) hbelow]
    linarith
