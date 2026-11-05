-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_ruin_truncated_raw_caplinear_value_L1_without_stopped_state_measurability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T00:57:56.810314+00:00
-- url     : https://prove2.me/submissions/a3f68d65-e0c0-4edf-8cc1-ffee4e01b6cb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_ruin_clock_discounted_exp_integrable_any_q
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_ruin_stopped_Levy_value_aestronglyMeasurable_from_exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- An exponential envelope yields L1 of the actual finite-horizon
ruin-stopped same-source comparison value without a stopped-X measurability
assumption. -/
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
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (V : ℝ → ℝ) (hVmeas : Measurable V)
    (K : ℝ) (hK : 0 ≤ K)
    (hEnvelope : ∀ z : ℝ, ‖V z‖ ≤ K * Real.exp z) :
    Integrable (fun ω => V (x + X.X (τ ω) ω)) P := by
  have hExpX : Integrable
      (fun ω => Real.exp (X.X (τ ω) ω)) P := by
    simpa using
      (avram_p4_f_assembly_original_ruin_clock_discounted_exp_integrable_any_q
        X x D n τ hτeq hτmeas hτstop 1 (by norm_num) 0)
  have hEnvelopeI : Integrable
      (fun ω => K * Real.exp (x + X.X (τ ω) ω)) P := by
    convert hExpX.const_mul (K * Real.exp x) using 1
    funext ω
    rw [Real.exp_add]
    ring
  have hXae : AEStronglyMeasurable (fun ω => X.X (τ ω) ω) P :=
    avram_p4_d_dividend_original_ruin_stopped_Levy_value_aestronglyMeasurable_from_exponential
      X x D n τ hτeq hτmeas hτstop
  have hAddAE : AEMeasurable (fun ω => x + X.X (τ ω) ω) P :=
    (measurable_const.aemeasurable).add hXae.aemeasurable
  have hVae : AEStronglyMeasurable
      (fun ω => V (x + X.X (τ ω) ω)) P :=
    (hVmeas.comp_aemeasurable hAddAE).aestronglyMeasurable
  apply hEnvelopeI.mono hVae
  filter_upwards [] with ω
  simpa [Real.norm_eq_abs, abs_mul, abs_of_nonneg hK,
    abs_of_pos (Real.exp_pos _)] using
    (hEnvelope (x + X.X (τ ω) ω))
