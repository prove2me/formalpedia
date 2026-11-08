-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gaussian10_original_stopped_bracket_L1_of_terminal_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T11:22:44.161319+00:00
-- url     : https://prove2.me/submissions/2e3cde08-077c-48dd-b5bc-fe0a19a9a017

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Under explicit original stopped-clock measurability, integrable terminal
quadratic energy dominates the capped stopped Gaussian bracket in L¹. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : ℝ≥0 × Ω → ℝ) (μtime : Measure ℝ≥0)
    (τ : Ω → ℝ≥0) (T : ℝ≥0)
    (hEnergy : ∀ ω, IntegrableOn
      (fun t : ℝ≥0 => (H (t, ω)) ^ 2)
      (Ioc (0 : ℝ≥0) T) μtime)
    (hStoppedMeas : Measurable
      (fun ω => ∫ t in Ioc (0 : ℝ≥0) (min (τ ω) T),
        (H (t, ω)) ^ 2 ∂μtime))
    (hTerminalL1 : Integrable
      (fun ω => ∫ t in Ioc (0 : ℝ≥0) T,
        (H (t, ω)) ^ 2 ∂μtime) P) :
    Integrable
      (fun ω => ∫ t in Ioc (0 : ℝ≥0) (min (τ ω) T),
        (H (t, ω)) ^ 2 ∂μtime) P := by
  apply hTerminalL1.mono hStoppedMeas.aestronglyMeasurable
  filter_upwards [] with ω
  have hcap : (∫ t in Ioc (0 : ℝ≥0) (min (τ ω) T),
        (H (t, ω)) ^ 2 ∂μtime) ≤
      ∫ t in Ioc (0 : ℝ≥0) T, (H (t, ω)) ^ 2 ∂μtime := by
    apply setIntegral_mono_set (hEnergy ω)
    · filter_upwards [] with t
      exact sq_nonneg (H (t, ω))
    · filter_upwards [] with t ht
      exact ⟨ht.1, ht.2.trans (min_le_right (τ ω) T)⟩
  have hzeroCap : 0 ≤ ∫ t in Ioc (0 : ℝ≥0) (min (τ ω) T),
        (H (t, ω)) ^ 2 ∂μtime := by
    apply integral_nonneg
    intro t
    exact sq_nonneg (H (t, ω))
  have hzeroTerm : 0 ≤ ∫ t in Ioc (0 : ℝ≥0) T,
        (H (t, ω)) ^ 2 ∂μtime := by
    apply integral_nonneg
    intro t
    exact sq_nonneg (H (t, ω))
  simpa only [Real.norm_eq_abs, abs_of_nonneg hzeroCap,
    abs_of_nonneg hzeroTerm] using hcap
