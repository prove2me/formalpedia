-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f9_original_finite_stopped_payoff_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T12:59:36.672207+00:00
-- url     : https://prove2.me/submissions/bb4ed2bc-ca97-47e7-903f-e74620dd67ad

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_avram_p4_f10_original_finite_stopped_discounted_payoff_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p4_f7_hjb_topcap_global_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_p4_f8_hjb_finite_terminal_envelope

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A measurable original-source terminal is uniformly bounded by its upper
exit envelope; global HJB nonnegativity gives an integrable terminal. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ ≠ 0)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hTop : C = ⊤) :
    ∀ (b : ℝ) (n : ℕ), 1 ≤ b →
      let τ : Ω → ℝ≥0∞ := fun ω =>
        min (twoSidedExitUpTimeCorrected X (b - 1) ω)
          (min (twoSidedExitDownTimeCorrected X (-1) ω) (n : ℝ≥0∞))
      Integrable (fun ω => Real.exp (-(q * ENNReal.toReal (τ ω))) *
        w (1 + X.X (ENNReal.toNNReal (τ ω)) ω)) P := by
  classical
  intro b n hb
  let τ : Ω → ℝ≥0∞ := fun ω =>
    min (twoSidedExitUpTimeCorrected X (b - 1) ω)
      (min (twoSidedExitDownTimeCorrected X (-1) ω) (n : ℝ≥0∞))
  let f : Ω → ℝ := fun ω =>
    Real.exp (-(q * ENNReal.toReal (τ ω))) *
      w (1 + X.X (ENNReal.toNNReal (τ ω)) ω)
  haveI : IsProbabilityMeasure P := X.isProbability
  have hmeas : Measurable f := by
    simpa only [f, τ] using
      avram_p4_f10_original_finite_stopped_discounted_payoff_measurable
        X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg
        hw_smooth hw_gen hw_grad hTop b n hb
  have hn := avram_p4_f7_hjb_topcap_global_nonnegative
    w C hw0 hw_cont hw_neg hw_smooth hw_grad hTop
  have hnonneg : ∀ ω, 0 ≤ f ω := by
    intro ω
    exact mul_nonneg (Real.exp_nonneg _) (hn _)
  have hB : ∀ ω, f ω ≤ w b := by
    intro ω
    have henu : ENNReal.ofReal (f ω) ≤ ENNReal.ofReal (w b) := by
      simpa only [f, τ] using
        avram_p4_f8_hjb_finite_terminal_envelope
          X hX w C hw0 hw_cont hw_neg hw_smooth hw_grad hTop
          q hq b n hb ω
    exact (ENNReal.ofReal_le_ofReal_iff (hn b)).mp henu
  change Integrable f P
  apply Integrable.of_bound hmeas.aestronglyMeasurable (w b)
  filter_upwards [] with ω
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hnonneg ω)] using hB ω
