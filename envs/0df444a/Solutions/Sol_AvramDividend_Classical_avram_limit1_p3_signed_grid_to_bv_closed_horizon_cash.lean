-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit1_p3_signed_grid_to_bv_closed_horizon_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T23:23:11.394637+00:00
-- url     : https://prove2.me/submissions/fc624ea3-35c8-471e-84e4-56df7aed176b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit1_original_bv_ubv_nonnegative_clock_cash_hjb_preflight
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_vanishing_error_grid_to_actual_prebudget
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_original_strict_expected_to_full_atom_ennreal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- From the literal P3 signed original Fatou grid obtain inclusive finite
    Stieltjes cash at the same horizon, preserving the horizon dividend atom. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (hGrid : ∃ F M B : ℕ → Ω → ℝ,
      (∀ n, Measurable (F n)) ∧
      (∀ n, Integrable (F n) P) ∧
      (∀ n, 0 ≤ᵐ[P] F n) ∧
      (∀ n, Integrable (fun ω => M n ω + B n ω) P ∧
        (∫ ω, M n ω + B n ω ∂P) ≤ 0) ∧
      (∀ n, ∀ᵐ ω ∂P, F n ω ≤ w x + (M n ω + B n ω)) ∧
      (∀ᵐ ω ∂P,
        let S : ℝ≥0 := ⟨T, hT⟩
        ENNReal.ofReal (
          (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
            ENNReal.ofReal (Real.exp (-(q * t)))
              ∂(dividendMeasure D ω)).toReal +
          (if (S : ℝ≥0∞) < ruinTime X x D ω then
            Real.exp (-(q * T)) * w (riskProcess X x D S ω)
          else 0)) ≤
        liminf (fun n => ENNReal.ofReal (F n ω)) atTop)) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal (w x) := by
  have hSmooth :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) := by
    constructor
    · intro hnBV
      exact (hnBV hBV).elim
    · intro _
      exact hw_smooth
  obtain ⟨τ, hτ, hτMeas, hτStop, W, Cash, Term, hW, hCash,
    hTerm, hTermMeas, hCashI, hGen, hGrad, hNonneg, hJump⟩ :=
    avram_limit1_original_bv_ubv_nonnegative_clock_cash_hjb_preflight
      X q w C hC hw0 hw_cont hw_neg hSmooth hw_hjb
      x hx hxc D hD 1
  obtain ⟨F, M, B, hFMeas, hFInt, hFPos, hMB, hGridBound, hFatou⟩ := hGrid
  let R : ℕ → Ω → ℝ := fun n ω => M n ω + B n ω
  have hR : ∀ n, Integrable (R n) P ∧
      (∫ ω, R n ω ∂P) ≤ 0 := by
    intro n
    simpa only [R] using hMB n
  have hBound : ∀ n, ∀ᵐ ω ∂P,
      F n ω ≤ w x + R n ω + (0 : ℝ) := by
    intro n
    filter_upwards [hGridBound n] with ω hω
    simpa only [R, add_zero] using hω
  have hZero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop
      (nhds (0 : ℝ)) := tendsto_const_nhds
  have hStrict :
      let S : ℝ≥0 := ⟨T, hT⟩
      (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω)
        else 0) ∂P) ≤ w x :=
    avram_p3_2_original_vanishing_error_grid_to_actual_prebudget
      X hBV x C D hD w hw_cont hw_neg hNonneg
      q hq.le T hT hTpos F R (fun _ => 0)
      hFMeas hFInt hFPos hR hZero hBound hFatou
  exact avram_bv_env3_original_strict_expected_to_full_atom_ennreal
    X hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hGrad
    x hx hxc D hD hJump T hT hTpos hStrict
