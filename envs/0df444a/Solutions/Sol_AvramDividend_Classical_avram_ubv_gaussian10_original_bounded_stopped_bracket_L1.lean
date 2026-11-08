-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gaussian10_original_bounded_stopped_bracket_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T11:56:57.403836+00:00
-- url     : https://prove2.me/submissions/36e23a79-9998-41e5-b95b-9ef96e6a44ae

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_original_bracket_progressive_of_continuous
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_original_stopped_bracket_L1_of_terminal_energy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A bounded stopping clock preserves L¹ of the original Gaussian bracket
under explicit square energy, time continuity and terminal L¹ hypotheses. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : ℝ≥0 × Ω → ℝ)
    (hH : Measurable[𝓕.rightCont.predictable] H)
    (μtime : Measure ℝ≥0) [SFinite μtime]
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hBound : ∀ ω, τ ω ≤ T)
    (hEnergy : ∀ ω, IntegrableOn
      (fun t : ℝ≥0 => (H (t, ω)) ^ 2)
      (Ioc (0 : ℝ≥0) T) μtime)
    (hContinuous : ∀ ω, Continuous (fun b : ℝ≥0 =>
      ∫ t in Ioc (0 : ℝ≥0) b, (H (t, ω)) ^ 2 ∂μtime))
    (hTerminalL1 : Integrable
      (fun ω => ∫ t in Ioc (0 : ℝ≥0) T,
        (H (t, ω)) ^ 2 ∂μtime) P) :
    Integrable (fun ω => ∫ t in Ioc (0 : ℝ≥0) (τ ω),
        (H (t, ω)) ^ 2 ∂μtime) P := by
  have hProg : IsStronglyProgressive 𝓕.rightCont (fun b ω =>
      ∫ t in Ioc (0 : ℝ≥0) b, (H (t, ω)) ^ 2 ∂μtime) :=
    avram_ubv_gaussian10_original_bracket_progressive_of_continuous
      X H hH μtime hContinuous
  have hStopped : Measurable (fun ω =>
      ∫ t in Ioc (0 : ℝ≥0) (min (τ ω) T),
        (H (t, ω)) ^ 2 ∂μtime) := by
    have hm : Measurable (stoppedValue
        (fun b ω => ∫ t in Ioc (0 : ℝ≥0) b,
          (H (t, ω)) ^ 2 ∂μtime)
        (fun ω => (τ ω : WithTop ℝ≥0))) :=
      (measurable_stoppedValue hProg hτ).mono
        hτ.measurableSpace_le le_rfl
    convert hm using 1
    funext ω
    simp only [min_eq_left (hBound ω), stoppedValue, WithTop.untopA]
    rw [WithTop.untopD_coe]
  have hL1 := avram_ubv_gaussian10_original_stopped_bracket_L1_of_terminal_energy
    X H μtime τ T hEnergy hStopped hTerminalL1
  convert hL1 using 1
  funext ω
  rw [min_eq_left (hBound ω)]
