-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_11_original_expected_stieltjes_horizon_mono
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:09:32.120931+00:00
-- url     : https://prove2.me/submissions/a26bcf28-d44b-4866-9518-cc6a92fffde9

import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_pathwise_stieltjes_horizon_mono
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Expected original-process Stieltjes reward is monotone in the real
    observation horizon, retaining right payout atoms at both endpoints. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (D : ℝ≥0 → Ω → ℝ) (σ : Ω → ℝ≥0∞)
    (q T U : ℝ) (hTU : T ≤ U) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (σ ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
    (∫⁻ ω, ∫⁻ t in paymentTimes (σ ω) ∩ Iic U,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) := by
  apply lintegral_mono
  intro ω
  exact avram_wave7_11_pathwise_stieltjes_horizon_mono
    D ω (σ ω) q T U hTU
