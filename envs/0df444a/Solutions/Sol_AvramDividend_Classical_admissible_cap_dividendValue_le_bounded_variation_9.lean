-- Prove2me | solution 9 for AvramDividend.Classical.admissible_cap_dividendValue_le_bounded_variation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T10:00:43.385191+00:00
-- url     : https://prove2.me/submissions/08203d36-4e60-470b-a1bb-8d04559627f6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_separate_gradient_right_atom_control
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_strict_preruin_closed_cap_C1_lower_envelope
import Theorems.Thm_AvramDividend_Classical_capped_riskProcess_range_before_ruin_including_zero
import Theorems.Thm_AvramDividend_Classical_avram_chat07b_original_BV_drift_envelope_branch_full_HJB_cash_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat05_bv_drift_envelope_complement_core
import Theorems.Thm_AvramDividend_Classical_dividendValue_eq_iSup_truncated
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
/-- BV original-source capped dividend verification by drift-envelope cases. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0) (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → X.GeneratorIntegrable w y ∧ max (X.generator w y - q * w y) (1 - deriv w y) = 0) (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    dividendValue X q x D ≤ ENNReal.ofReal (w x) := by
  have hwGrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y := by
    intro y hy hyC
    have hMax := (hw_hjb y hy hyC).2
    have hSlope : (1 : ℝ) - deriv w y ≤ 0 := by
      calc
        1 - deriv w y ≤
            max (X.generator w y - q * w y) (1 - deriv w y) :=
          le_max_right _ _
        _ = 0 := hMax
    linarith
  have hwGen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0 := by
    intro y hy hyC
    rcases hw_hjb y hy hyC with ⟨hInt, hGenMax⟩
    refine ⟨hInt, ?_⟩
    calc
      X.generator w y - q * w y ≤
          max (X.generator w y - q * w y) (1 - deriv w y) :=
        le_max_left _ _
      _ = 0 := hGenMax
  have hSmoothBoth :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) := by
    constructor
    · intro hnBV
      exact False.elim (hnBV hBV)
    · intro _
      exact hw_smooth
  have hJump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) → rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) - w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)) :=
    avram_wave5_03_original_separate_gradient_right_atom_control
      X w C hC hw_cont hSmoothBoth hwGrad x hxc D hD
  have hNonneg : ∀ ω (t : ℝ≥0), 0 < t →
        (t : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D t ω) := by
    intro ω t ht hBefore
    have hLower :=
      avram_p3_g2_original_strict_preruin_closed_cap_C1_lower_envelope
        X C hC w hw_cont hw_smooth hwGrad x D hD
        ω t ht hBefore
    have hRange :=
      capped_riskProcess_range_before_ruin_including_zero
        X x hx C hxc D hD ω t hBefore
    linarith only [hLower, hRange.1, hw0]
  have hFinite (T : ℝ≥0) :
      (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ), ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal (w x) := by
    by_cases hEnvelope : x + (T : ℝ) * X.drift ≤ w x
    · exact avram_chat07b_original_BV_drift_envelope_branch_full_HJB_cash_bound
        X hX hBV x hx C hxc D hD q hq.le T w hEnvelope
    · exact avram_wave6_chat05_bv_drift_envelope_complement_core
        X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
        hwGen hwGrad x hx hxc D hD hNonneg hJump
        (T : ℝ) T.property hEnvelope
  rw [dividendValue_eq_iSup_truncated X q x D hD.1]
  refine iSup_le fun n => ?_
  simpa using hFinite (n : ℝ≥0)
