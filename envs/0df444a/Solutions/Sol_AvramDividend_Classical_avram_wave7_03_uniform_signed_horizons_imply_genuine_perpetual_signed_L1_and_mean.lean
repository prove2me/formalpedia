-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_uniform_signed_horizons_imply_genuine_perpetual_signed_L1_and_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:51:43.649667+00:00
-- url     : https://prove2.me/submissions/4667b717-6e3c-4a66-85c7-6400a6370687

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_dividendValue_finite_iff_uniform_signed_horizon_mean_bounded
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_signed_stieltjes_L1_and_exact_outer_mean_of_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Original signed finite-horizon budgets imply true unrestricted
    source Stieltjes L1 and expected real/ENNReal equality. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (B : ℝ)
    (hBudget : ∀ n : ℕ,
      (∫ ω, (∫ t in
          paymentTimes (ruinTime X x D ω) ∩ Iic (((n + 1 : ℕ) : ℝ)),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ B) :
    Integrable (fun ω : Ω =>
      ∫ t in paymentTimes (ruinTime X x D ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P ∧
    dividendValue X q x D =
      ENNReal.ofReal
        (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by
  have hFinite : dividendValue X q x D < ⊤ :=
    (avram_wave7_03_original_dividendValue_finite_iff_uniform_signed_horizon_mean_bounded
      X x C D hD q hq).2 ⟨B, hBudget⟩
  exact avram_wave7_03_original_perpetual_signed_stieltjes_L1_and_exact_outer_mean_of_finite
    X x D hD.1.1 q hFinite
