-- Prove2me | solution 12 for AvramDividend.Classical.admissible_cap_truncated_dividendValue_le_bounded_variation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T12:25:58.755441+00:00
-- url     : https://prove2.me/submissions/a3a6d8bc-cbf7-4253-a0c8-605c14a932b0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_local_verification_stochastic_core_side_conditions
import Theorems.Thm_AvramDividend_Classical_local_verification_hjb_candidate_lower_bound_on_cap
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_complete_closed_horizon_sharp_expected_drift_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat05_bv_drift_envelope_complement_core

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

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
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  have hsmooth :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) := by
    constructor
    · intro hnot
      exact False.elim (hnot hBV)
    · intro _
      exact hw_smooth
  obtain ⟨hgen, hgrad, hnonneg, hjump⟩ :=
    local_verification_stochastic_core_side_conditions
      X q w C hw_cont hw0 hsmooth hw_hjb x hxc D hD
  classical
  have hDriftBudget :
      x + T * X.drift ≤ w x →
        (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
          ENNReal.ofReal (w x) := by
    intro hEnvelope
    let S : ℝ≥0 := ⟨T, hT⟩
    have hRaw :=
      avram_wave3_03_bv_complete_closed_horizon_sharp_expected_drift_budget
        X hX hBV x hx C hxc D hD q (le_of_lt hq) S
    have hCoe : (S : ℝ) = T := rfl
    rw [hCoe] at hRaw
    exact hRaw.trans (ENNReal.ofReal_le_ofReal hEnvelope)
  by_cases hTzero : T = 0
  · have hW : x + w 0 ≤ w x :=
      (local_verification_hjb_candidate_lower_bound_on_cap
        X q w C hw_cont hw0 hsmooth hw_hjb x hx hxc).1
    apply hDriftBudget
    rw [hTzero, zero_mul, add_zero]
    exact (le_add_of_nonneg_right hw0).trans hW
  · by_cases hEnvelope : x + T * X.drift ≤ w x
    · exact hDriftBudget hEnvelope
    · exact avram_wave6_chat05_bv_drift_envelope_complement_core
        X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
        hgen hgrad x hx hxc D hD hnonneg hjump T hT hEnvelope
