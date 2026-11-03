-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_11_original_expected_terminal_stieltjes_atom_survival_formula
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T19:14:57.924961+00:00
-- url     : https://prove2.me/submissions/04938bea-78bc-4c4c-a144-07003d3cc0ed

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_positive_horizon_terminal_atom_survival_indicator_formula
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Expected true source endpoint cash is exactly the original
    dividend measure singleton times its pre-ruin survival indicator. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (q T : ℝ) (hT : 0 < T) :
    (∫⁻ ω, ∫⁻ t in
      (paymentTimes (ruinTime X x D ω) ∩ Iic T) ∩ {T},
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) =
    ∫⁻ ω, if ENNReal.ofReal T < ruinTime X x D ω then
      (dividendMeasure D ω) ({T} : Set ℝ) *
        ENNReal.ofReal (Real.exp (-(q * T))) else 0 ∂P := by
  apply lintegral_congr
  intro ω
  exact avram_wave7_11_positive_horizon_terminal_atom_survival_indicator_formula
    D ω (ruinTime X x D ω) q T hT
