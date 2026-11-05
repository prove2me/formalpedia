-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_auto_compact_L_and_R
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T12:31:38.588567+00:00
-- url     : https://prove2.me/submissions/abe2407c-b28b-402b-9c0c-8045a14ce321

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_ENNReal_positive_cap_interior_isOpen
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_original_bv_ENNReal_cap_compact_C1_lipschitz
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_negative_zero_uniform_value_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hbC : ENNReal.ofReal b < C) :
    ∃ L R : ℝ, 0 ≤ L ∧ 0 ≤ R ∧
      (∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b,
        |w u - w v| ≤ L * |u - v|) ∧
      (∀ v : ℝ, v ≤ b → |w v| ≤ R) := by
  have halfr : a / 2 < b := by linarith
  have hband : Icc (a / 2) b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by
    intro u hu
    rcases mem_Icc.mp hu with ⟨hlo, hhi⟩
    constructor
    · linarith
    · exact lt_of_le_of_lt (ENNReal.ofReal_mono hhi) hbC
  obtain ⟨L, hL, hLip⟩ :=
    avram_wave6_chat09_original_bv_ENNReal_cap_compact_C1_lipschitz
      X hBV w C (a / 2) b halfr
      (avram_wave6_chat09_ENNReal_positive_cap_interior_isOpen C)
      hband (fun _ => hwC1)
  obtain ⟨R, hR, hBound⟩ :=
    avram_p3_bv_original_negative_zero_uniform_value_bound
      w hw_cont hw_neg b (by linarith)
  exact ⟨L, R, hL, hR, hLip, hBound⟩
