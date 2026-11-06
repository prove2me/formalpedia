-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit1_original_signed_grids_all_horizons_to_perpetual_value
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T23:28:19.40819+00:00
-- url     : https://prove2.me/submissions/c453a24e-e93b-4060-9386-ddbb15cfa8ff

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit1_p3_signed_grid_to_bv_closed_horizon_cash
import Theorems.Thm_AvramDividend_Classical_dividendValue_eq_iSup_truncated

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Exact signed original BV grids at every positive horizon imply the full
    dividend value bound, retaining zero-time and positive horizon atoms. -/
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
    (hGrid : ∀ (T : ℝ) (hT : 0 ≤ T), 0 < T →
      ∃ F M B : ℕ → Ω → ℝ,
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
    dividendValue X q x D ≤ ENNReal.ofReal (w x) := by
  have hClosed (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T) :
      (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal (w x) :=
    avram_limit1_p3_signed_grid_to_bv_closed_horizon_cash
      X hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_hjb
      x hx hxc D hD T hT hTpos (hGrid T hT hTpos)
  rw [dividendValue_eq_iSup_truncated X q x D hD.1]
  refine iSup_le fun n => ?_
  have hn : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_succ n
  calc
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P)
        ≤ (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Iic (((n + 1 : ℕ) : ℝ)),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω) ∂P) := by
              apply lintegral_mono
              intro ω
              apply lintegral_mono_set
              intro t ht
              exact ⟨ht.1, ht.2.trans hn⟩
    _ ≤ ENNReal.ofReal (w x) :=
      hClosed (((n + 1 : ℕ) : ℝ)) (by positivity) (by positivity)
