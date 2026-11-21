-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_inf20_original_finitecap_bounded_nearzero_true_generator_mark_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T16:42:17.058206+00:00
-- url     : https://prove2.me/submissions/460aa4b8-37bd-46ba-bd00-fc475d5791da

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_finitecap_complete_mark_overshoot_envelope
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
    (hy : C.toReal < y) (hz : z < 0) (hzsmall : -δ < z) :
    SpectrallyNegativeLevy.generatorIntegrand
      (fun t => if t ≤ C.toReal then w t else w C.toReal + (t - C.toReal))
      y z ≤ 0 := by
  have hCpos : 0 < C := by
    by_contra hnot
    have hzero : C = 0 := le_antisymm (le_of_not_gt hnot) bot_le
    have hreal : C.toReal = 0 := by simp [hzero]
    linarith
  have hsmall : -1 < z := by linarith
  have hmem : z ∈ Ioo (-1 : ℝ) 1 := ⟨hsmall, by linarith⟩
  have hpost : 0 ≤ y + z := by linarith
  have h :=
    avram_mix_inf20_original_finitecap_complete_mark_overshoot_envelope
      C hCpos hFinite w hw0 hw_cont hw_neg hw_smooth hw_grad y z hy
  have hm : max 0 (-(y + z)) = 0 := max_eq_left (neg_nonpos.mpr hpost)
  have hh : SpectrallyNegativeLevy.generatorIntegrand
      (fun t => if t ≤ C.toReal then w t else w C.toReal + (t - C.toReal))
      y z ≤ max 0 (-(y + z)) := by
    simpa [SpectrallyNegativeLevy.generatorIntegrand, hmem] using h
  rw [hm] at hh
  exact hh
