-- Prove2me | solution 1 for AvramDividend.Classical.avram_b27_original_size2_jumps_large_sum_eq_count
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T08:46:47.135119+00:00
-- url     : https://prove2.me/submissions/aabf232d-6931-4756-83bf-aa8018514499

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_a22_original_largejump_raw_source_equals_physical_finite_mark_sum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (t : ℝ≥0) (F : Finset ℝ≥0)
    (hF : ∀ u : ℝ≥0, u ∈ F ↔ 0 < u ∧ u ≤ t ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0)
    (hSize : ∀ u ∈ F,
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = -2) :
    avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω =
      -2 * (F.card : ℝ) := by
  have hRaw :=
    avram_a22_original_largejump_raw_source_equals_physical_finite_mark_sum
      X ω t F hF
  calc
    avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω =
      ∑ u ∈ F,
        if X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤ -1
        then X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
        else 0 := hRaw
    _ = ∑ u ∈ F, (-2 : ℝ) := by
      apply Finset.sum_congr rfl
      intro u hu
      have hMark := hSize u hu
      simp [hMark]
    _ = -2 * (F.card : ℝ) := by
      simp only [Finset.sum_const_zero, Finset.sum_const, nsmul_eq_mul]
      ring
