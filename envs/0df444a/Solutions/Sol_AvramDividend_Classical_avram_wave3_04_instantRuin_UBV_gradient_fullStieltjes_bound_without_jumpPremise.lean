-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_04_instantRuin_UBV_gradient_fullStieltjes_bound_without_jumpPremise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T22:21:41.201977+00:00
-- url     : https://prove2.me/submissions/7be7660d-0131-4549-9b9a-2f7e6524e932

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_ubv_HJB_candidate_dominates_initial_capital
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_instant_ruin_closed_horizon_initial_budget

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The repaired UBV HJB candidate dominates the complete actual
discounted original Stieltjes dividend reward after immediate ruin,
without separately postulating a dividend-jump HJB premise. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hxc : ENNReal.ofReal x ≤ C) (hx : 0 ≤ x)
    (w : ℝ → ℝ) (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (hRuin : ∀ᵐ ω ∂P, ruinTime X x D ω = 0)
    (T : ℝ≥0) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hcapvalue : x ≤ w x :=
    avram_wave3_04_ubv_HJB_candidate_dominates_initial_capital
      C w hw0 hw_cont hw_smooth hw_grad x hx hxc
  have hPay : (fun ω => ∫⁻ t in
      paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
      ≤ᵐ[P] (fun _ => ENNReal.ofReal x) := by
    filter_upwards [hRuin] with ω hr
    exact avram_wave3_03_bv_instant_ruin_closed_horizon_initial_budget
      X x C hxc D hD q T ω hr
  calc
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
        ∫⁻ _ : Ω, ENNReal.ofReal x ∂P := lintegral_mono_ae hPay
    _ = ENNReal.ofReal x := by simp
    _ ≤ ENNReal.ofReal (w x) := ENNReal.ofReal_le_ofReal hcapvalue
