-- Prove2me | solution 13 for AvramDividend.Classical.admissible_cap_dividendValue_le_bounded_variation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:00:53.432364+00:00
-- url     : https://prove2.me/submissions/798aaa25-3fd0-4b1f-880b-ec995bf5c925
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_zero_or_strict_preruin_C1_canonical_hjump_without_standing
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_strict_preruin_closed_cap_C1_lower_envelope
import Theorems.Thm_AvramDividend_Classical_capped_riskProcess_range_before_ruin_including_zero
import Theorems.Thm_AvramDividend_Classical_avram_integration_p3_original_strict_source_residual_witness
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_prebudget_L1
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_strict_HJB_to_signed_full
import Theorems.Thm_AvramDividend_Classical_avram_limit2_bv_hjb_signed_terminal_to_perpetual

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Original BV value bound from the first stochastic residual, bypassing P3's Open wrappers. -/
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
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    dividendValue X q x D ≤ ENNReal.ofReal (w x) := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hGrad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y := by
    intro y hy hyC
    have h := (hw_hjb y hy hyC).2
    have hs : (1 : ℝ) - deriv w y ≤ 0 := by
      calc
        1 - deriv w y ≤
            max (X.generator w y - q * w y) (1 - deriv w y) :=
          le_max_right _ _
        _ = 0 := h
    linarith
  have hGen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0 := by
    intro y hy hyC
    rcases hw_hjb y hy hyC with ⟨hi, hm⟩
    refine ⟨hi, ?_⟩
    exact (le_max_left _ _).trans_eq hm
  have hJump :=
    avram_p3_g2_original_zero_or_strict_preruin_C1_canonical_hjump_without_standing
      X C hC w hw_cont hw_smooth hGrad x hxc D hD
  have hNonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω) := by
    intro ω t ht hBefore
    have hLower :=
      avram_p3_g2_original_strict_preruin_closed_cap_C1_lower_envelope
        X C hC w hw_cont hw_smooth hGrad x D hD ω t ht hBefore
    have hRange := capped_riskProcess_range_before_ruin_including_zero
      X x hx C hxc D hD ω t hBefore
    linarith only [hLower, hRange.1, hw0]
  have hBudget : ∀ (T : ℝ) (hT : 0 ≤ T), 0 < T →
      let S : ℝ≥0 := ⟨T, hT⟩
      let Term : Ω → ℝ := fun ω =>
        if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (x + X.X S ω - rightLimit D S ω)
        else 0
      (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal ∂P) +
      (∫ ω, Term ω ∂P) ≤ w x := by
    intro T hT hTpos
    obtain ⟨E, hEint, hEmean, hPath⟩ :=
      avram_integration_p3_original_strict_source_residual_witness
        X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
        hGen hGrad x hx hxc D hD hNonneg hJump T hT hTpos
    dsimp only at hPath
    have hInt := avram_p3_bv_original_prebudget_L1
      X hBV x C D hD w hw_cont hw_neg q (le_of_lt hq) T hT
    dsimp only at hInt
    have hLe := integral_mono_ae hInt
      ((integrable_const (w x)).add hEint) hPath
    have hRight : (∫ ω : Ω, w x + E ω ∂P) =
        w x + (∫ ω : Ω, E ω ∂P) := by
      simp [integral_add (integrable_const _) hEint]
    simp only [Pi.add_apply] at hLe
    rw [hRight] at hLe
    have hStrict := hLe.trans (add_le_of_nonpos_right hEmean)
    exact avram_p3_bv_strict_HJB_to_signed_full
      X hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hGrad
      x D hD hJump T hT hTpos hStrict
  exact (avram_limit2_bv_hjb_signed_terminal_to_perpetual
    X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
    hw_hjb x hx hxc D hD hBudget).2
