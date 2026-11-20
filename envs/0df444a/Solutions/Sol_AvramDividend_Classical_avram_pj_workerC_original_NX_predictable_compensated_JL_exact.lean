-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_original_NX_predictable_compensated_JL_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T07:56:13.946972+00:00
-- url     : https://prove2.me/submissions/120b2822-e3a8-4320-8d2c-b344b951c517

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_levy_negative_mark_sigmaFinite
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_NX_ae_negative_jumps
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_compensated_two_measure_JL_negative_mark_identity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0)
    (η : ℝ) (hη : 0 < η) (hηone : η < 1)
    (S d : (ℝ≥0 × ℝ) → ℝ) :
    let μT : Measure ℝ≥0 :=
      ((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal
    let NX : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict
        {t : ℝ≥0 | 0 < t ∧ X.X t ω -
          Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0}).map
        (fun t : ℝ≥0 => (t, X.X t ω -
          Function.leftLim (fun s : ℝ≥0 => X.X s ω) t)))
    let CN : Measure (ℝ≥0 × ℝ) :=
      μT.prod (X.ν.restrict (Iio (0 : ℝ)))
    Integrable (fun p => S p -
      (if -1 < p.2 then p.2 * d p else 0)) NX →
    Integrable (fun p =>
      if p.2 ∈ Ioo (-1 : ℝ) (-η) then p.2 * d p else 0) NX →
    Integrable (fun p => S p -
      (if -1 < p.2 then p.2 * d p else 0)) CN →
    Integrable (fun p =>
      if p.2 ∈ Ioo (-1 : ℝ) (-η) then p.2 * d p else 0) CN →
    ((∫ p, S p - (if -1 < p.2 then p.2 * d p else 0) ∂NX) -
      (∫ p, S p - (if -1 < p.2 then p.2 * d p else 0) ∂CN)) +
    ((∫ p, if p.2 ∈ Ioo (-1 : ℝ) (-η) then p.2 * d p else 0 ∂NX) -
      (∫ p, if p.2 ∈ Ioo (-1 : ℝ) (-η) then p.2 * d p else 0 ∂CN)) =
    (∫ p, S p - (if -η ≤ p.2 then p.2 * d p else 0) ∂NX) -
    (∫ p, S p - (if -η ≤ p.2 then p.2 * d p else 0) ∂CN) := by
  intro μT NX CN hHM hLM hHN hLN
  have hMneg : ∀ᵐ p ∂NX, p.2 < (0 : ℝ) := by
    exact AvramDividend.Classical.avram_pj_workerC_original_NX_ae_negative_jumps X ω
  have hNneg : ∀ᵐ p ∂CN, p.2 < (0 : ℝ) := by
    letI : SigmaFinite X.ν :=
      AvramDividend.Classical.avram_p3_e_compensator_original_levy_negative_mark_sigmaFinite X
    haveI : SFinite (X.ν.restrict (Iio (0 : ℝ))) := inferInstance
    change ∀ᵐ p ∂(μT.prod (X.ν.restrict (Iio (0 : ℝ)))), p.2 < (0 : ℝ)
    rw [Measure.ae_prod_iff_ae_ae]
    filter_upwards [] with t
    exact ae_restrict_mem measurableSet_Iio
    all_goals exact measurableSet_Iio.preimage measurable_snd
  exact
    AvramDividend.Classical.avram_pj_workerC_compensated_two_measure_JL_negative_mark_identity
      NX CN η S d hη hηone hMneg hNneg hHM hLM hHN hLN

