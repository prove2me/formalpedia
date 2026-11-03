-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_full_ruin_deterministic_horizon_mean_consumption
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T12:53:37.389636+00:00
-- url     : https://prove2.me/submissions/9fb451ad-2817-428b-a6fb-39ecd5040984

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_full_ruin_bounded_clock_unconditional_mean_eq
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Consumer example: direct deterministic-horizon full original stopped cash. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) =
    ENNReal.ofReal
      (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by
  simpa only using
    (avram_wave7_03_original_full_ruin_bounded_clock_unconditional_mean_eq
      X x C D hD q hq T (fun _ => T)
      (fun _ => le_rfl) (by exact measurable_const))
