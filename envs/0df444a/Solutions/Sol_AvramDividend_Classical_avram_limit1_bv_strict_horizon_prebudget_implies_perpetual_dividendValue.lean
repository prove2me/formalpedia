-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit1_bv_strict_horizon_prebudget_implies_perpetual_dividendValue
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T23:08:06.555798+00:00
-- url     : https://prove2.me/submissions/b5dc6994-7075-466c-91b9-9e7f6fcd39c6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit1_original_bv_ubv_nonnegative_clock_cash_hjb_preflight
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_original_strict_expected_to_full_atom_ennreal
import Theorems.Thm_AvramDividend_Classical_dividendValue_eq_iSup_truncated

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- A genuine original-process BV strict stopped budget at every positive
    horizon implies the perpetual dividend-value bound. The source preflight
    supplies the actual HJB derivative and time-zero jump inequalities. -/
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
    (hBudget : ∀ (T : ℝ) (hT : 0 ≤ T), 0 < T →
      let S : ℝ≥0 := ⟨T, hT⟩
      (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω)
         else 0) ∂P) ≤ w x) :
    dividendValue X q x D ≤ ENNReal.ofReal (w x) := by
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
  have hClosed (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T) :
      (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal (w x) :=
    avram_bv_env3_original_strict_expected_to_full_atom_ennreal
      X hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hGrad
      x hx hxc D hD hJump T hT hTpos (hBudget T hT hTpos)
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
