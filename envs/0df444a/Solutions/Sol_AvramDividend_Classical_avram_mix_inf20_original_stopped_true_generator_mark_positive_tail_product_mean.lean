-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_inf20_original_stopped_true_generator_mark_positive_tail_product_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T20:46:16.987079+00:00
-- url     : https://prove2.me/submissions/f855ba84-a64b-4799-a849-899b85349df6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_abovecap_true_truncated_jump_positive_tail_unit_domination
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (C : ℝ≥0∞) (hFinite : C ≠ ⊤)
    (w : ℝ → ℝ) (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ u : ℝ, u < 0 → w u = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (δ : ℝ) (hδ : 0 < δ) (hδone : δ ≤ 1) (hδcap : δ ≤ C.toReal)
    (μ : Measure ((ℝ≥0 × Ω) × ℝ)) :
    let V : ℝ → ℝ := fun t =>
      if t ≤ C.toReal then w t else w C.toReal + (t - C.toReal)
    let Y : ℝ≥0 × Ω → ℝ := fun p =>
      Function.leftLim
        (fun t : ℝ≥0 => x + X.X t p.2 - rightLimit D t p.2) p.1
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if C.toReal < Y p.1 ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          SpectrallyNegativeLevy.generatorIntegrand V (Y p.1) p.2
      else 0
    let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if C.toReal < Y p.1 ∧ p.2 < 0 ∧ p.2 ≤ -δ then
        Real.exp (-(q * (p.1.1 : ℝ)))
      else 0
    Integrable H μ → Integrable G μ →
      (∫ p, H p ∂μ) ≤ (∫ p, G p ∂μ) := by
  dsimp only
  intro hHI hGI
  apply integral_mono hHI hGI
  intro p
  by_cases hy : C.toReal <
      Function.leftLim
        (fun t : ℝ≥0 => x + X.X t p.1.2 - rightLimit D t p.1.2) p.1.1 ∧
      p.2 < 0
  · have hmark :=
      avram_mix_inf20_original_abovecap_true_truncated_jump_positive_tail_unit_domination
        C hFinite w hw0 hw_cont hw_neg hw_smooth hw_grad
        δ _ p.2 hδ hδone hδcap hy.1 hy.2
    by_cases htail : p.2 ≤ -δ
    · have hmarkPos : SpectrallyNegativeLevy.generatorIntegrand
          (fun t => if t ≤ C.toReal then w t else w C.toReal + (t - C.toReal))
          (Function.leftLim
            (fun t : ℝ≥0 => x + X.X t p.1.2 - rightLimit D t p.1.2)
            p.1.1) p.2 ≤ 1 := by
        simpa only [if_pos htail] using hmark
      have hguard : C.toReal <
            Function.leftLim
              (fun t : ℝ≥0 => x + X.X t p.1.2 - rightLimit D t p.1.2)
              p.1.1 ∧ p.2 < 0 ∧ p.2 ≤ -δ :=
        ⟨hy.1, hy.2, htail⟩
      simp only [if_pos hy, if_pos hguard]
      simpa only [mul_one] using
        (mul_le_mul_of_nonneg_left hmarkPos
          (le_of_lt (Real.exp_pos (-(q * (p.1.1 : ℝ))))))
    · have hnot : ¬ (C.toReal <
          Function.leftLim
            (fun t : ℝ≥0 => x + X.X t p.1.2 - rightLimit D t p.1.2) p.1.1 ∧
          p.2 < 0 ∧ p.2 ≤ -δ) := by
          intro h
          exact htail h.2.2
      simp only [if_pos hy, if_neg hnot]
      have hh : SpectrallyNegativeLevy.generatorIntegrand
        (fun t => if t ≤ C.toReal then w t else w C.toReal + (t - C.toReal))
        (Function.leftLim
          (fun t : ℝ≥0 => x + X.X t p.1.2 - rightLimit D t p.1.2)
          p.1.1) p.2 ≤ 0 := by simpa only [if_neg htail] using hmark
      exact mul_nonpos_of_nonneg_of_nonpos
        (le_of_lt (Real.exp_pos (-(q * (p.1.1 : ℝ))))) hh
  · have hnot : ¬ (C.toReal <
        Function.leftLim
          (fun t : ℝ≥0 => x + X.X t p.1.2 - rightLimit D t p.1.2) p.1.1 ∧
        p.2 < 0 ∧ p.2 ≤ -δ) := by
        intro h
        exact hy ⟨h.1, h.2.1⟩
    simp only [if_neg hy, if_neg hnot, le_refl]
