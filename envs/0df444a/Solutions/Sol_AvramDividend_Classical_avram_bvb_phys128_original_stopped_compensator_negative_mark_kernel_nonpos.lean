-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys128_original_stopped_compensator_negative_mark_kernel_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T12:53:44.166088+00:00
-- url     : https://prove2.me/submissions/d0fbd58f-b023-4dc1-a6ca-45f9fab6aa31

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys88_original_closed_cap_negative_mark_value_increment_nonpos

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped NNReal ENNReal
noncomputable section

/-- The entire original stopped discounted negative-mark kernel is
nonpositive, including the genuine zero and closed-cap boundary. -/
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
    (q T : ℝ) (t : ℝ≥0) (b z : ℝ) (τ : ℝ≥0∞) :
    (if 0 < t ∧ (t : ℝ) < T ∧ (t : ℝ≥0∞) ≤ τ ∧
          0 ≤ b ∧ ENNReal.ofReal b ≤ C ∧ z < 0 then
        Real.exp (-(q * (t : ℝ))) * (w (b + z) - w b)
      else 0) ≤ 0 := by
  classical
  split_ifs with h
  · rcases h with ⟨_, _, _, hb, hbC, hz⟩
    have hmark :=
      AvramDividend.Classical.avram_bvb_phys88_original_closed_cap_negative_mark_value_increment_nonpos
        C hC w hw_cont hw0 hw_neg hw_smooth hw_grad b z hb hbC hz
    exact mul_nonpos_of_nonneg_of_nonpos
      (le_of_lt (Real.exp_pos _)) hmark
  · exact le_rfl
