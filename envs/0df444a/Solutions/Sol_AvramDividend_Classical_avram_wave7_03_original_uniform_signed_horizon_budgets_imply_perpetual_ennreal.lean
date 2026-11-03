-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_uniform_signed_horizon_budgets_imply_perpetual_ennreal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T13:36:33.418456+00:00
-- url     : https://prove2.me/submissions/4ddabeb5-7ec8-4e5d-af05-72e7a4ea3a99

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_cash_eq_iSup_real_stieltjes_means
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Uniform real Stieltjes budgets on original ruin-stopped integer horizons
    imply the complete perpetual original ENNReal dividend budget. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (B : ℝ)
    (hBudget : ∀ n : ℕ,
      (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω) ∩
          Iic (((n + 1 : ℕ) : ℝ)),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ B) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal B := by
  rw [avram_wave7_03_original_perpetual_cash_eq_iSup_real_stieltjes_means
    X x C D hD q hq]
  exact iSup_le (fun n => ENNReal.ofReal_le_ofReal (hBudget n))
