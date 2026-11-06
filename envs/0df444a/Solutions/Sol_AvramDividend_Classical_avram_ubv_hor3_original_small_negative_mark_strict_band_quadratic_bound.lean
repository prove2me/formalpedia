-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_hor3_original_small_negative_mark_strict_band_quadratic_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:02:34.148196+00:00
-- url     : https://prove2.me/submissions/f15ee23d-203e-479f-8f33-8d09ba0e7ec8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_positive_band_lipschitz_source
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (δ K : ℝ) (hδ : 0 < δ) (hδK : δ ≤ K)
    (hK : ENNReal.ofReal K < C) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ u ∈ Icc δ K, ∀ z : ℝ,
        -(δ / 2) ≤ z → z ≤ 0 →
        (w (u + z) - w u) ^ 2 ≤ M * z ^ 2 := by
  have hHalf : 0 < δ / 2 := by positivity
  have hHalfK : δ / 2 ≤ K := by linarith
  obtain ⟨B, hLip⟩ :=
    avram_p4_f3_original_positive_band_lipschitz_source
      w C hw_smooth (δ / 2) K hHalf hHalfK hK
  refine ⟨B ^ 2, sq_nonneg _, ?_⟩
  intro u hu z hzlo hzhi
  have huHalf : u ∈ Icc (δ / 2) K := by
    constructor
    · have huLower : δ ≤ u := hu.1
      linarith
    · exact hu.2
  have huzHalf : u + z ∈ Icc (δ / 2) K := by
    constructor
    · have huLower : δ ≤ u := hu.1
      linarith
    · have huUpper : u ≤ K := hu.2
      linarith
  have hAbs : |w (u + z) - w u| ≤ B * |z| := by
    simpa only [add_sub_cancel_left] using
      hLip u huHalf (u + z) huzHalf
  have hRightNN : 0 ≤ B * |z| :=
    le_trans (abs_nonneg _) hAbs
  have hMul : 0 ≤
      (B * |z| - |w (u + z) - w u|) *
        (B * |z| + |w (u + z) - w u|) :=
    mul_nonneg (sub_nonneg.mpr hAbs)
      (add_nonneg hRightNN (abs_nonneg _))
  have hWSq : |w (u + z) - w u| ^ 2 =
      (w (u + z) - w u) ^ 2 := sq_abs _
  have hZSq : |z| ^ 2 = z ^ 2 := sq_abs _
  nlinarith
