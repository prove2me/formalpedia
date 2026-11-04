-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_joint_L1_actual_stopped_integrals_expectation_convergence_auto_meas
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T15:24:31.762926+00:00
-- url     : https://prove2.me/submissions/0ab4a10f-64e9-4179-b791-5752eebaac6d

import Mathlib.Algebra.Notation.Indicator
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_joint_L1_all_stopped_integrals_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_joint_L1_expected_clock_limit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Joint L¹ alone, with the original source dividend strategy, ensures physical stopped expectation convergence. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [SFinite P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hDiv : IsDividendStrategy 𝓕 D)
    (μ : Measure ℝ≥0) [SFinite μ]
    (f : ℝ≥0 × Ω → ℝ) (hf : Integrable f (μ.prod P)) :
    Integrable (fun ω => ∫ t : ℝ≥0,
      ({s : ℝ≥0 | (s : ℝ≥0∞) < ruinTime X x D ω}).indicator
        (fun t => f (t, ω)) t ∂μ) P ∧
    Tendsto (fun n : ℕ => ∫ ω, ∫ t : ℝ≥0,
      ({s : ℝ≥0 | (s : ℝ≥0∞) <
        min (ruinTime X x D ω) (n : ℝ≥0∞)}).indicator
        (fun t => f (t, ω)) t ∂μ ∂P)
      atTop (nhds (∫ ω, ∫ t : ℝ≥0,
      ({s : ℝ≥0 | (s : ℝ≥0∞) < ruinTime X x D ω}).indicator
        (fun t => f (t, ω)) t ∂μ ∂P)) := by
  have hAll :=
    avram_p4_e_localise_original_joint_L1_all_stopped_integrals_integrable
      P X x D hDiv μ f hf
  have hFiniteMeas : ∀ n : ℕ,
      AEStronglyMeasurable (fun ω => ∫ t : ℝ≥0,
        ({s : ℝ≥0 | (s : ℝ≥0∞) <
          min (ruinTime X x D ω) (n : ℝ≥0∞)}).indicator
          (fun t => f (t, ω)) t ∂μ) P := by
    intro n
    simpa only [Set.indicator, Set.mem_setOf_eq] using
      (hAll.2 n).aestronglyMeasurable
  have hFullMeas : AEStronglyMeasurable (fun ω => ∫ t : ℝ≥0,
      ({s : ℝ≥0 | (s : ℝ≥0∞) < ruinTime X x D ω}).indicator
        (fun t => f (t, ω)) t ∂μ) P := by
    simpa only [Set.indicator, Set.mem_setOf_eq] using
      hAll.1.aestronglyMeasurable
  exact avram_p4_e_localise_original_joint_L1_expected_clock_limit
    P X x C D hD μ f hf hFiniteMeas hFullMeas