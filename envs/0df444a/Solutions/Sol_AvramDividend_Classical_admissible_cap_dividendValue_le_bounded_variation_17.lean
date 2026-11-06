-- Prove2me | solution 17 for AvramDividend.Classical.admissible_cap_dividendValue_le_bounded_variation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T16:52:02.551442+00:00
-- url     : https://prove2.me/submissions/578734c9-9f5d-48d3-b83d-35bf866c3e87
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_zero_or_strict_preruin_C1_canonical_hjump_without_standing
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_strict_preruin_closed_cap_C1_lower_envelope
import Theorems.Thm_AvramDividend_Classical_capped_riskProcess_range_before_ruin_including_zero
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_source_signed_fatou_grid_certificate
import Theorems.Thm_AvramDividend_Classical_avram_limit2_bv_source_witness_to_perpetual_value

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Direct BV-value consumer of the original signed finite-grid source witness. -/
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
  have hGrad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y := by
    intro y hy hyC
    have hs : (1 : ℝ) - deriv w y ≤ 0 := by
      calc
        1 - deriv w y ≤
            max (X.generator w y - q * w y) (1 - deriv w y) :=
          le_max_right _ _
        _ = 0 := (hw_hjb y hy hyC).2
    linarith
  have hGen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0 := by
    intro y hy hyC
    rcases hw_hjb y hy hyC with ⟨hi, hm⟩
    exact ⟨hi, (le_max_left _ _).trans_eq hm⟩
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
    have hRange :=
      capped_riskProcess_range_before_ruin_including_zero
        X x hx C hxc D hD ω t hBefore
    linarith only [hLower, hRange.1, hw0]
  refine avram_limit2_bv_source_witness_to_perpetual_value
    X q hq w x D hD.1 hNonneg ?_
  intro T hT hTpos
  exact avram_p3_bv_original_source_signed_fatou_grid_certificate
    X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
    hGen hGrad x hx hxc D hD hNonneg hJump T hT hTpos
