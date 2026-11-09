-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_zero13_original_stopping_future_nojump_drift_probability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T23:52:05.393341+00:00
-- url     : https://prove2.me/submissions/8ae48977-8393-4ed4-ac4f-3eb00069d2ca

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_full_future_source_law
import Theorems.Thm_AvramDividend_Classical_bv_actual_residual_increment_zero_probability
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04_source_rightCont_levy_lift
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_stoppedFuturePath_measurable
import Theorems.Thm_AvramDividend_Classical_levy_wholePath_measurable
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (T : ℝ≥0) :
    P.real {ω : Ω |
      ((T : ℝ) * X.drift -
        (X.X (τ ω + T) ω - X.X (τ ω) ω)) -
      (((0 : ℝ≥0) : ℝ) * X.drift -
        (X.X (τ ω + 0) ω - X.X (τ ω) ω)) = 0} =
    Real.exp (-((T : ℝ) * (X.ν (Iio (0 : ℝ))).toReal)) := by
  classical
  let B : Set (ℝ≥0 → ℝ) := {g |
    ((T : ℝ) * X.drift - g T) -
      (((0 : ℝ≥0) : ℝ) * X.drift - g 0) = 0}
  have hB : MeasurableSet B := by
    have hMeas : Measurable (fun g : ℝ≥0 → ℝ =>
        ((T : ℝ) * X.drift - g T) -
          (((0 : ℝ≥0) : ℝ) * X.drift - g 0)) :=
      (measurable_const.sub (measurable_pi_apply T)).sub
        (measurable_const.sub (measurable_pi_apply 0))
    exact hMeas (measurableSet_singleton (0 : ℝ))
  let F : Ω → (ℝ≥0 → ℝ) := fun ω t =>
    X.X (τ ω + t) ω - X.X (τ ω) ω
  let G : Ω → (ℝ≥0 → ℝ) := fun ω t => X.X t ω
  have hF : Measurable F := by
    obtain ⟨Y, hYpath, -, -, -⟩ :=
      avram_wave5_04_source_rightCont_levy_lift X
    simpa only [F, hYpath] using
      (levy_finiteStopping_stoppedFuturePath_measurable
        Y τ (isStoppingTime_withTop_of_le_events τ hτ))
  have hG : Measurable G := by
    simpa only [G] using (levy_wholePath_measurable X)
  have hLaw : Measure.map F P = Measure.map G P := by
    simpa only [F, G] using
      (avram_wave6_03_original_rightCont_stopped_full_future_source_law X τ hτ)
  have hProbB : P (F ⁻¹' B) = P (G ⁻¹' B) := by
    have hEq := congrArg (fun m : Measure (ℝ≥0 → ℝ) => m B) hLaw
    simpa only [Measure.map_apply hF hB, Measure.map_apply hG hB]
      using hEq
  have hProbReal : P.real (F ⁻¹' B) = P.real (G ⁻¹' B) := by
    exact congrArg ENNReal.toReal hProbB
  have hOrigin :=
    bv_actual_residual_increment_zero_probability
      X hBV hFinite 0 T zero_le
  change P.real {ω : Ω |
      ((T : ℝ) * X.drift -
        (X.X (τ ω + T) ω - X.X (τ ω) ω)) -
      (((0 : ℝ≥0) : ℝ) * X.drift -
        (X.X (τ ω + 0) ω - X.X (τ ω) ω)) = 0} =
    P.real {ω : Ω |
      ((T : ℝ) * X.drift - X.X T ω) -
      (((0 : ℝ≥0) : ℝ) * X.drift - X.X 0 ω) = 0}
    at hProbReal
  exact hProbReal.trans (by simpa only [tsub_zero] using hOrigin)
