-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_env3_original_signed_fatou_grids_to_closed_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:36:09.292176+00:00
-- url     : https://prove2.me/submissions/471087a9-2c6e-4c07-a028-3ccbdbcb12cc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_vanishing_error_grid_to_actual_prebudget
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_original_strict_expected_to_full_atom_ennreal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- The original signed finite-grid Fatou certificate, if constructed,
    supplies the entire inclusive-horizon Stieltjes budget. No assumed
    martingale or source-grid existence is hidden in this theorem. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (F M B : ℕ → Ω → ℝ)
    (hFm : ∀ n, Measurable (F n))
    (hFi : ∀ n, Integrable (F n) P)
    (hFn : ∀ n, 0 ≤ᵐ[P] F n)
    (hR : ∀ n, Integrable (fun ω => M n ω + B n ω) P ∧
      (∫ ω, M n ω + B n ω ∂P) ≤ 0)
    (hBound0 : ∀ n, ∀ᵐ ω ∂P,
      F n ω ≤ w x + (M n ω + B n ω))
    (hFatou : ∀ᵐ ω ∂P,
      let S : ℝ≥0 := ⟨T, hT⟩
      ENNReal.ofReal (
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω)
        else 0)) ≤
      liminf (fun n => ENNReal.ofReal (F n ω)) atTop) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  classical
  have hErr : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds
  have hBound : ∀ n, ∀ᵐ ω ∂P,
      F n ω ≤ w x + (M n ω + B n ω) + 0 := by
    intro n
    filter_upwards [hBound0 n] with ω hω
    simpa only [add_zero] using hω
  have hStrict := avram_p3_2_original_vanishing_error_grid_to_actual_prebudget
    X hBV x C D hD w hw_cont hw_neg hw_nonneg
    q (le_of_lt hq) T hT hTpos
    F (fun n ω => M n ω + B n ω) (fun _ => (0 : ℝ))
    hFm hFi hFn hR hErr hBound hFatou
  exact avram_bv_env3_original_strict_expected_to_full_atom_ennreal
    X hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_grad
    x hx hxc D hD hjump T hT hTpos hStrict
