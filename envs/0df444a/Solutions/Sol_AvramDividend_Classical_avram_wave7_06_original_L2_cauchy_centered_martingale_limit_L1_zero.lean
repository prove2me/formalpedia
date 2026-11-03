-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_L2_cauchy_centered_martingale_limit_L1_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:44:40.008583+00:00
-- url     : https://prove2.me/submissions/7100ca77-fd00-4ec1-91df-7a5710516a14

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.UniformSpace.Cauchy
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_probability_l2_expectation_continuous_original_space

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- A Cauchy family of centred stopped approximants on the original Lévy
probability space has a centred L² limit, hence a valid L¹ mean passage. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (M : ℕ → Lp ℝ (2 : ℝ≥0∞) P)
    (hCauchy : CauchySeq M)
    (hCentered : ∀ n, (∫ ω, M n ω ∂P) = 0) :
    ∃ L : Lp ℝ (2 : ℝ≥0∞) P,
      Tendsto M Filter.atTop (𝓝 L) ∧
      (∫ ω, L ω ∂P) = 0 := by
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨L, hLimit⟩ := cauchySeq_tendsto_of_complete hCauchy
  have hCont : Continuous (fun F : Lp ℝ (2 : ℝ≥0∞) P =>
      ∫ ω, F ω ∂P) :=
    avram_wave4_p1_probability_l2_expectation_continuous_original_space P
  have hMeanLimit : Tendsto (fun n => ∫ ω, M n ω ∂P)
      Filter.atTop (𝓝 (∫ ω, L ω ∂P)) :=
    hCont.continuousAt.tendsto.comp hLimit
  have hConst : (fun n : ℕ => ∫ ω, M n ω ∂P) =
      (fun _ : ℕ => (0 : ℝ)) := by
    funext n
    exact hCentered n
  rw [hConst] at hMeanLimit
  have hZero : (∫ ω, L ω ∂P) = 0 :=
    tendsto_nhds_unique hMeanLimit tendsto_const_nhds
  exact ⟨L, hLimit, hZero⟩
