-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_11_original_expected_finite_horizon_strict_clock_plus_surviving_atom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T19:19:58.17946+00:00
-- url     : https://prove2.me/submissions/4865c24c-11ee-41c9-8fff-c29c447e1ada

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_original_expected_positive_horizon_exact_endpoint_decomposition
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_original_expected_terminal_stieltjes_atom_survival_formula
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Complete exact expected source UBV finite-horizon Stieltjes
    decomposition: strict stopped reward plus the original survivor-only
    horizon dividend atom. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q T : ℝ) (hT : 0 < T) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) =
    (∫⁻ ω, ∫⁻ t in
      paymentTimes (min (ruinTime X x D ω) (ENNReal.ofReal T)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) +
    (∫⁻ ω, if ENNReal.ofReal T < ruinTime X x D ω then
      (dividendMeasure D ω) ({T} : Set ℝ) *
        ENNReal.ofReal (Real.exp (-(q * T))) else 0 ∂P) := by
  rw [avram_wave7_11_original_expected_positive_horizon_exact_endpoint_decomposition
    X x D hD q T hT]
  rw [avram_wave7_11_original_expected_terminal_stieltjes_atom_survival_formula
    X x D q T hT]
