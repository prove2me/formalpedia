-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_dividendValue_finite_iff_uniform_signed_horizon_mean_bounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:32:43.307463+00:00
-- url     : https://prove2.me/submissions/8e913f46-1641-4e9f-93d4-0808bdce0367

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_cash_eq_iSup_real_stieltjes_means
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_uniform_signed_horizon_budgets_imply_dividendValue_le
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- The canonical perpetual original dividend value is finite exactly
    when all original finite-horizon signed Stieltjes expected payouts
    admit a common real upper bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) :
    (dividendValue X q x D < ⊤) ↔
    ∃ B : ℝ, ∀ n : ℕ,
      (∫ ω, (∫ t in
          paymentTimes (ruinTime X x D ω) ∩ Iic (((n + 1 : ℕ) : ℝ)),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ B := by
  have hBridge :
      dividendValue X q x D =
        ⨆ n : ℕ, ENNReal.ofReal
          (∫ ω, (∫ t in
              paymentTimes (ruinTime X x D ω) ∩
                Iic (((n + 1 : ℕ) : ℝ)),
            Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by
    exact avram_wave7_03_original_perpetual_cash_eq_iSup_real_stieltjes_means
      X x C D hD q hq
  constructor
  · intro hFinite
    refine ⟨(dividendValue X q x D).toReal, ?_⟩
    intro n
    have hMeanNonneg : 0 ≤
        (∫ ω, (∫ t in
            paymentTimes (ruinTime X x D ω) ∩
              Iic (((n + 1 : ℕ) : ℝ)),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by
      apply integral_nonneg
      intro ω
      apply integral_nonneg
      intro t
      exact (Real.exp_pos (-(q * t))).le
    have hOfRealLe : ENNReal.ofReal
        (∫ ω, (∫ t in
            paymentTimes (ruinTime X x D ω) ∩
              Iic (((n + 1 : ℕ) : ℝ)),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤
        dividendValue X q x D := by
      rw [hBridge]
      exact le_iSup_of_le n le_rfl
    have hToRealLe := ENNReal.toReal_mono (ne_of_lt hFinite) hOfRealLe
    simpa only [ENNReal.toReal_ofReal hMeanNonneg] using hToRealLe
  · rintro ⟨B, hBudget⟩
    have hLe :=
      avram_wave7_03_original_uniform_signed_horizon_budgets_imply_dividendValue_le
        X x C D hD q hq B hBudget
    exact lt_of_le_of_lt hLe ENNReal.ofReal_lt_top
