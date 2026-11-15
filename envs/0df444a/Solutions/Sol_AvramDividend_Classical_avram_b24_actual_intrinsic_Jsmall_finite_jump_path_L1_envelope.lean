-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_actual_intrinsic_Jsmall_finite_jump_path_L1_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:14:17.137513+00:00
-- url     : https://prove2.me/submissions/20da4e31-5d8c-4d24-a89e-1ea82a3d061e

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_b24_finite_true_negative_smallmark_total_amplitude_le_actual_jump_count
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {α : Type*}
    (S : Finset α) (z : α → ℝ) (T : ℝ≥0) (t : ℝ≥0)
    (ht : t ≤ T) (d j : ℝ)
    (hj : j = (∑ i ∈ S, if -1 < z i ∧ z i < 0 then z i else 0) -
      (t : ℝ) * d) :
    ‖j‖ ≤ (S.card : ℝ) + (T : ℝ) * ‖d‖ := by
  rw [hj]
  have hMark :=
    AvramDividend.Classical.avram_b24_finite_true_negative_smallmark_total_amplitude_le_actual_jump_count
      S z
  have htReal : (t : ℝ) ≤ (T : ℝ) := by exact_mod_cast ht
  have htNonneg : (0 : ℝ) ≤ (t : ℝ) := NNReal.coe_nonneg t
  have hTnorm : ‖(t : ℝ)‖ = (t : ℝ) :=
    Real.norm_eq_abs (t : ℝ) ▸ abs_of_nonneg htNonneg
  have hDrift : ‖(t : ℝ) * d‖ ≤ (T : ℝ) * ‖d‖ := by
    rw [norm_mul, hTnorm]
    exact mul_le_mul_of_nonneg_right htReal (norm_nonneg d)
  calc
    ‖(∑ i ∈ S, if -1 < z i ∧ z i < 0 then z i else 0) -
      (t : ℝ) * d‖ ≤
        ‖∑ i ∈ S, if -1 < z i ∧ z i < 0 then z i else 0‖ +
          ‖(t : ℝ) * d‖ := norm_sub_le _ _
    _ ≤ (S.card : ℝ) + (T : ℝ) * ‖d‖ :=
      add_le_add hMark hDrift
