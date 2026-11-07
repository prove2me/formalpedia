-- Prove2me | solution 33 for AvramDividend.Classical.admissible_cap_truncated_dividendValue_le_bounded_variation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T18:51:26.906462+00:00
-- url     : https://prove2.me/submissions/638bdc54-ade9-434c-8a18-2fa8fc9cc489
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_04_original_BV_positive_horizon_signed_stopped_HJB_budget
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_original_positive_horizon_signed_HJB_to_closed_cash
import Theorems.Thm_AvramDividend_Classical_avram_wave7_09_corrected_positive_cap_bv_parent_zero_horizon_full_stieltjes_bound
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_zero_or_strict_preruin_C1_canonical_hjump_without_standing
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_corrected_boundary_hjb_pre_ruin_terminal_nonneg
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  have hgen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0 := by
    intro y hy hyC
    obtain ⟨hI, hMax⟩ := hw_hjb y hy hyC
    exact ⟨hI, (max_le_iff.mp (le_of_eq hMax)).1⟩
  have hgrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y := by
    intro y hy hyC
    have hMax := (hw_hjb y hy hyC).2
    have hLe := (max_le_iff.mp (le_of_eq hMax)).2
    linarith
  have hNonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω) := by
    intro ω t ht0 ht
    exact avram_wave6_08_original_corrected_boundary_hjb_pre_ruin_terminal_nonneg
      X x C hC hxc D hD w hw0 hw_cont hw_smooth hgrad ω t ht
  have hJump :=
    avram_p3_g2_original_zero_or_strict_preruin_C1_canonical_hjump_without_standing
      X C hC w hw_cont hw_smooth hgrad x hxc D hD
  by_cases hzero : T = 0
  · subst T
    exact avram_wave7_09_corrected_positive_cap_bv_parent_zero_horizon_full_stieltjes_bound
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
      hgen hgrad x hxc D hD hNonneg
  · have hTpos : 0 < T := lt_of_le_of_ne hT (Ne.symm hzero)
    have hSigned :=
      avram_wave8_04_original_BV_positive_horizon_signed_stopped_HJB_budget
        X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
        hgen hgrad x hx hxc D hD hNonneg hJump T hT hTpos
    exact avram_bv_env3_original_positive_horizon_signed_HJB_to_closed_cash
      X hBV q (le_of_lt hq) w C hC hw_cont hw0 hw_neg hw_smooth
      hgrad x hx hxc D hD T hT hTpos hSigned
