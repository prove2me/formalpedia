-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_e_compensator_original_horizon_drift_L1_of_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T13:22:35.685496+00:00
-- url     : https://prove2.me/submissions/5d6f6784-fa6c-4db5-b223-47a3f1cf0f7f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
{Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
{𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
(T : ℝ≥0) (F : ℝ≥0 × Ω → ℝ)
(hFm : AEStronglyMeasurable F ((((volume : Measure ℝ).restrict
  (Set.Icc 0 (T : ℝ))).map Real.toNNReal).prod P))
(C : ℝ) (hFbound : ∀ p : ℝ≥0 × Ω, |F p| ≤ C) :
Integrable F ((((volume : Measure ℝ).restrict
  (Set.Icc 0 (T : ℝ))).map Real.toNNReal).prod P) := by
  letI : IsProbabilityMeasure P := X.isProbability
  haveI : IsFiniteMeasure ((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))) :=
    Real.isFiniteMeasure_restrict_Icc 0 (T : ℝ)
  haveI : IsFiniteMeasure (((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal) :=
    inferInstance
  apply Integrable.of_bound hFm C
  exact Filter.Eventually.of_forall (by
    intro p
    simpa [Real.norm_eq_abs] using hFbound p)
