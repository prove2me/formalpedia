-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_ruin_stopped_Levy_value_aestronglyMeasurable_from_exponential
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T00:47:09.983775+00:00
-- url     : https://prove2.me/submissions/a8f78ed3-c05e-4492-9414-495058b450b0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_ruin_clock_discounted_exp_integrable_any_q

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The genuine original ruin-stopped Lévy value is almost-everywhere strongly
measurable: its already-proved integrable exponential determines the value via
the measurable logarithm, without a second stopped-process assumption. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω : Ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    AEStronglyMeasurable (fun ω => X.X (τ ω) ω) P := by
  have hExp : Integrable (fun ω => Real.exp (X.X (τ ω) ω)) P := by
    simpa using
      (avram_p4_f_assembly_original_ruin_clock_discounted_exp_integrable_any_q
        X x D n τ hτeq hτmeas hτstop 1 (by norm_num) 0)
  have hExpAE : AEMeasurable (fun ω => Real.exp (X.X (τ ω) ω)) P :=
    hExp.aestronglyMeasurable.aemeasurable
  have hLogAE : AEMeasurable
      (fun ω => Real.log (Real.exp (X.X (τ ω) ω))) P :=
    Real.measurable_log.comp_aemeasurable hExpAE
  have hLogStrong := hLogAE.aestronglyMeasurable
  simpa only [Real.log_exp] using hLogStrong
