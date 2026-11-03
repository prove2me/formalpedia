-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_predictable_weight_centered_future_increment_L2_isometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:58:32.075186+00:00
-- url     : https://prove2.me/submissions/41d0a737-2c5f-418e-b9cd-e86ebcd420e4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_centered_future_L2_variance_stationarity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- Original source predictable-weight L² isometry for an entire centred
future increment, with exact stationary variance and source filtration. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s t : ℝ≥0)
    (W : Ω → ℝ)
    (hWPast : Measurable[𝓕 s] W)
    (hWSq : Integrable (fun ω => (W ω)^2) P)
    (hXI : Integrable (X.X t) P)
    (hXSq : Integrable (fun ω => (X.X t ω)^2) P) :
    (∫ ω,
      (W ω * (X.X (s + t) ω - X.X s ω -
        (∫ η, X.X t η ∂P)))^2 ∂P) =
      (∫ ω, (W ω)^2 ∂P) *
      (∫ ω, (X.X t ω - (∫ η, X.X t η ∂P))^2 ∂P) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let A : Ω → ℝ := fun ω => X.X (s + t) ω - X.X s ω
  let m : ℝ := ∫ η, X.X t η ∂P
  obtain ⟨hVarInt, hVarEq⟩ :=
    avram_wave7_06_original_centered_future_L2_variance_stationarity
      X s t hXI hXSq
  have hSquare : Integrable (fun ω => (A ω - m)^2) P := hVarInt
  have hVariance :
      (∫ ω, (A ω - m)^2 ∂P) =
        (∫ ω, (X.X t ω - m)^2 ∂P) := hVarEq
  have hWComap : MeasurableSpace.comap W inferInstance ≤ 𝓕 s :=
    (measurable_iff_comap_le).mp hWPast
  have hRawIndep : Indep
      (MeasurableSpace.comap A inferInstance) (𝓕 s) P := by
    simpa only [A] using X.indepIncrements s (s + t) (by simp)
  have hFunIndep : IndepFun W A P := by
    apply (IndepFun_iff_Indep W A P).2
    exact indep_of_indep_of_le hRawIndep.symm hWComap le_rfl
  have hWeightSquare : Measurable (fun y : ℝ => y^2) :=
    measurable_id.pow_const 2
  have hCenterSquare : Measurable (fun y : ℝ => (y - m)^2) :=
    (measurable_id.sub measurable_const).pow_const 2
  have hSquaresIndep :
      IndepFun (fun ω => (W ω)^2)
        (fun ω => (A ω - m)^2) P := by
    simpa only [Function.comp_def] using
      hFunIndep.comp hWeightSquare hCenterSquare
  have hFactor := hSquaresIndep.integral_mul_eq_mul_integral
    hWSq.aestronglyMeasurable hSquare.aestronglyMeasurable
  change (∫ ω, (W ω)^2 * (A ω - m)^2 ∂P) =
    (∫ ω, (W ω)^2 ∂P) * (∫ ω, (A ω - m)^2 ∂P) at hFactor
  change (∫ ω, (W ω * (A ω - m))^2 ∂P) =
    (∫ ω, (W ω)^2 ∂P) *
      (∫ ω, (X.X t ω - m)^2 ∂P)
  calc
    (∫ ω, (W ω * (A ω - m))^2 ∂P) =
        ∫ ω, (W ω)^2 * (A ω - m)^2 ∂P := by
      congr 1
      funext ω
      ring
    _ = (∫ ω, (W ω)^2 ∂P) *
          (∫ ω, (A ω - m)^2 ∂P) := hFactor
    _ = (∫ ω, (W ω)^2 ∂P) *
          (∫ ω, (X.X t ω - m)^2 ∂P) := by rw [hVariance]
