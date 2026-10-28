-- Prove2me | solution 1 for AvramDividend.Classical.constant_restricted_real_law_pointwise_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T23:14:17.462985+00:00
-- url     : https://prove2.me/submissions/fd75e1a9-7d1c-4e59-8fe8-483512c4b0ef

import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.NNReal
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Theorems.Thm_AvramDividend_Classical_lintegral_stoppedEvent_reward_tendsto_of_bounded
import Theorems.Thm_AvramDividend_Classical_compactTest_lintegral_scalar_factor_implies_measure_smul
import Theorems.Thm_AvramDividend_Classical_compactTest_nnreal_uniformBound_finiteLintegral
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (A : Set Ω) (hA : MeasurableSet A)
    (Yₙ : ℕ → Ω → ℝ) (Y : Ω → ℝ)
    (hYn : ∀ n, Measurable (Yₙ n)) (hY : Measurable Y)
    (hlim : ∀ ω, Tendsto (fun n => Yₙ n ω) atTop (𝓝 (Y ω)))
    (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hlaw : ∀ n, Measure.map (Yₙ n) (μ.restrict A) = μ A • ν) :
    Measure.map Y (μ.restrict A) = μ A • ν := by
  classical
  haveI : (Measure.map Y (μ.restrict A)).Regular := inferInstance
  haveI : ((μ A) • ν).Regular :=
    Measure.Regular.smul (measure_ne_top μ A)
  apply AvramDividend.Classical.compactTest_lintegral_scalar_factor_implies_measure_smul
    (μ A)
  intro g
  let F : ℝ → ℝ≥0∞ := fun y => ((g y : ℝ≥0) : ℝ≥0∞)
  have hFc : Continuous F := ENNReal.continuous_coe.comp g.continuous
  have hFm : Measurable F := hFc.measurable
  let C : ℝ≥0∞ :=
    ((nndist (0 : BoundedContinuousFunction ℝ ℝ≥0)
      g.toBoundedContinuousFunction : ℝ≥0) : ℝ≥0∞)
  have hEnv := AvramDividend.Classical.compactTest_nnreal_uniformBound_finiteLintegral
    μ (measure_ne_top μ Set.univ) g
  have hMeas (n : ℕ) : Measurable
      (Set.indicator A (fun ω => F (Yₙ n ω))) :=
    (hFm.comp (hYn n)).indicator hA
  have hConverge (ω : Ω) :
      Tendsto (fun n => F (Yₙ n ω)) atTop (𝓝 (F (Y ω))) :=
    (hFc.tendsto (Y ω)).comp (hlim ω)
  have hDCT :=
    AvramDividend.Classical.lintegral_stoppedEvent_reward_tendsto_of_bounded
      μ A (fun n ω => F (Yₙ n ω)) (fun ω => F (Y ω))
      hMeas hConverge C (fun n ω => hEnv.1 _) hEnv.2
  have hEach (n : ℕ) :
      (∫⁻ ω, Set.indicator A (fun ω => F (Yₙ n ω)) ω ∂μ) =
      μ A * (∫⁻ y, F y ∂ν) := by
    rw [lintegral_indicator hA]
    rw [← lintegral_map hFm (hYn n)]
    rw [hlaw n, lintegral_smul_measure]
    simp only [smul_eq_mul]
  have hConstant :
      (fun n : ℕ => ∫⁻ ω, Set.indicator A
        (fun ω => F (Yₙ n ω)) ω ∂μ) =
      (fun _ : ℕ => μ A * (∫⁻ y, F y ∂ν)) := by
    funext n
    exact hEach n
  rw [hConstant] at hDCT
  have hResult :
      (∫⁻ ω, Set.indicator A (fun ω => F (Y ω)) ω ∂μ) =
        μ A * (∫⁻ y, F y ∂ν) :=
    tendsto_nhds_unique hDCT tendsto_const_nhds
  change (∫⁻ y, F y ∂(Measure.map Y (μ.restrict A))) =
    μ A * (∫⁻ y, F y ∂ν)
  rw [lintegral_map hFm hY]
  exact (lintegral_indicator hA (fun ω => F (Y ω))).symm.trans hResult
