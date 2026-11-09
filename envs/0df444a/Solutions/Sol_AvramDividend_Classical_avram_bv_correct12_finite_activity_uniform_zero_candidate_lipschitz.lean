-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_correct12_finite_activity_uniform_zero_candidate_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T22:38:46.975105+00:00
-- url     : https://prove2.me/submissions/7c9bbd09-ca7f-4013-9733-0c179723901a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_correct12_finite_activity_uniform_zero_gradient_ceiling

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (b : ℝ) (hb : 0 ≤ b) (hbC : ENNReal.ofReal b < C) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ b →
        w t - w s ≤ L * (t - s) := by
  classical
  obtain ⟨L, hL0, hL⟩ :=
    avram_bv_correct12_finite_activity_uniform_zero_gradient_ceiling
      X hX hBV hFinite q hq w C hC hw_cont hw0 hw_neg
      hw_smooth hw_gen hw_grad b hb
  refine ⟨L, hL0, ?_⟩
  intro s t hs hst htb
  rcases eq_or_lt_of_le hst with heq | hlt
  · subst t
    simp
  have hcont : ContinuousOn w (Icc s t) := by
    apply hw_cont.mono
    intro y hy
    exact le_trans hs hy.1
  have hsub : Ioo s t ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by
    intro y hy
    refine ⟨lt_of_le_of_lt hs hy.1, ?_⟩
    exact lt_of_le_of_lt
      (ENNReal.ofReal_le_ofReal (le_trans (le_of_lt hy.2) htb)) hbC
  have hdiff : DifferentiableOn ℝ w (Ioo s t) :=
    hw_smooth.differentiableOn_one.mono hsub
  obtain ⟨c, hc, hSlope⟩ := exists_deriv_eq_slope w hlt hcont hdiff
  have hcC : ENNReal.ofReal c < C :=
    lt_of_le_of_lt (ENNReal.ofReal_le_ofReal
      (le_trans (le_of_lt hc.2) htb)) hbC
  have hcBound : deriv w c ≤ L :=
    hL c (lt_of_le_of_lt hs hc.1) (le_trans (le_of_lt hc.2) htb) hcC
  have hpos : 0 < t - s := sub_pos.mpr hlt
  calc
    w t - w s = deriv w c * (t - s) := by
      rw [hSlope]
      exact (div_mul_cancel₀ (w t - w s) (ne_of_gt hpos)).symm
    _ ≤ L * (t - s) := mul_le_mul_of_nonneg_right hcBound hpos.le
