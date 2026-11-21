-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_inf20_original_abovecap_true_truncated_jump_positive_tail_unit_domination
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T16:42:09.862581+00:00
-- url     : https://prove2.me/submissions/bd070e3c-add2-48ca-9849-803e9994c5c3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_finitecap_complete_mark_overshoot_envelope
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_finitecap_abovebarrier_all_negative_raw_marks_nonpos
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    (C : ℝ≥0∞) (hFinite : C ≠ ⊤)
    (w : ℝ → ℝ) (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ u : ℝ, u < 0 → w u = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (δ y z : ℝ) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hδcap : δ ≤ C.toReal)
    (hy : C.toReal < y) (hz : z < 0) :
    SpectrallyNegativeLevy.generatorIntegrand
      (fun t => if t ≤ C.toReal then w t else w C.toReal + (t - C.toReal))
      y z ≤ if z ≤ -δ then 1 else 0 := by
  have hCpos : 0 < C := by
    by_contra hc
    have hzero : C = 0 := le_antisymm (le_of_not_gt hc) bot_le
    have hreal : C.toReal = 0 := by simp [hzero]
    linarith
  have hypos : 0 < y := lt_trans (lt_of_lt_of_le hδ hδcap) hy
  by_cases hsmall : -1 < z
  · have hmem : z ∈ Ioo (-1 : ℝ) 1 := ⟨hsmall, by linarith⟩
    have h :=
      avram_mix_inf20_original_finitecap_complete_mark_overshoot_envelope
        C hCpos hFinite w hw0 hw_cont hw_neg hw_smooth hw_grad y z hy
    have hh : SpectrallyNegativeLevy.generatorIntegrand
        (fun t => if t ≤ C.toReal then w t else w C.toReal + (t - C.toReal))
        y z ≤ max 0 (-(y + z)) := by
      simpa [SpectrallyNegativeLevy.generatorIntegrand, hmem] using h
    by_cases htail : z ≤ -δ
    · have hm : max 0 (-(y + z)) ≤ 1 := by
        apply max_le (by norm_num)
        linarith
      simp only [if_pos htail]
      exact le_trans hh hm
    · have hpost : 0 ≤ y + z := by
        have hzδ : -δ < z := lt_of_not_ge htail
        linarith
      have hm : max 0 (-(y + z)) = 0 := max_eq_left (neg_nonpos.mpr hpost)
      simp only [if_neg htail]
      rw [hm] at hh
      exact hh
  · have hnot : z ∉ Ioo (-1 : ℝ) 1 := by
      intro hzmem
      exact hsmall hzmem.1
    have h :=
      avram_mix_inf20_original_finitecap_abovebarrier_all_negative_raw_marks_nonpos
        C hCpos hFinite w hw0 hw_cont hw_neg hw_smooth hw_grad y z hy hz
    have hh : SpectrallyNegativeLevy.generatorIntegrand
        (fun t => if t ≤ C.toReal then w t else w C.toReal + (t - C.toReal))
        y z ≤ 0 := by
      simpa [SpectrallyNegativeLevy.generatorIntegrand, hnot] using h
    have htail : z ≤ -δ := by
      have hz1 : z ≤ -1 := le_of_not_gt hsmall
      linarith
    simp only [if_pos htail]
    linarith
