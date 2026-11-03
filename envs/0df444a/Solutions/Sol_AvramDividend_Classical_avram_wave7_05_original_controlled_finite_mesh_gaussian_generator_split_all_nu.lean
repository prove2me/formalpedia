-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_05_original_controlled_finite_mesh_gaussian_generator_split_all_nu
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T14:53:32.8108+00:00
-- url     : https://prove2.me/submissions/08ac7574-7c2a-4950-8fab-dd41f9a8027c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_actual_discounted_ruin_stopped_predividend_generator_gaussian_split_all_nu

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (T : ℝ≥0) (S : Finset ι) (t : ι → ℝ≥0) (ω : Ω) :
    let y : ι → ℝ := fun i => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) (t i)
    let k : ι → ℝ := fun i =>
      if t i ≤ T then
        (if (t i : ℝ≥0∞) ≤ ruinTime X x D ω then 1 else 0) else 0
    (∑ i ∈ S,
      k i * (Real.exp (-(q * ((t i : ℝ≥0) : ℝ))) *
        (X.generator w (y i) - q * w (y i)))) =
      (∑ i ∈ S,
        k i * (Real.exp (-(q * ((t i : ℝ≥0) : ℝ))) *
          (X.σ ^ 2 / 2 * iteratedDeriv 2 w (y i)))) +
      (∑ i ∈ S,
        k i * (Real.exp (-(q * ((t i : ℝ≥0) : ℝ))) *
          (X.c * deriv w (y i) +
            (∫ z in Iio (0 : ℝ),
              SpectrallyNegativeLevy.generatorIntegrand w (y i) z ∂X.ν) -
              q * w (y i)))) := by
  classical
  let y : ι → ℝ := fun i => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) (t i)
  let k : ι → ℝ := fun i =>
    if t i ≤ T then
      (if (t i : ℝ≥0∞) ≤ ruinTime X x D ω then 1 else 0) else 0
  change (∑ i ∈ S,
      k i * (Real.exp (-(q * ((t i : ℝ≥0) : ℝ))) *
        (X.generator w (y i) - q * w (y i)))) =
      (∑ i ∈ S,
        k i * (Real.exp (-(q * ((t i : ℝ≥0) : ℝ))) *
          (X.σ ^ 2 / 2 * iteratedDeriv 2 w (y i)))) +
      (∑ i ∈ S,
        k i * (Real.exp (-(q * ((t i : ℝ≥0) : ℝ))) *
          (X.c * deriv w (y i) +
            (∫ z in Iio (0 : ℝ),
              SpectrallyNegativeLevy.generatorIntegrand w (y i) z ∂X.ν) -
              q * w (y i))))
  calc
    (∑ i ∈ S,
      k i * (Real.exp (-(q * ((t i : ℝ≥0) : ℝ))) *
        (X.generator w (y i) - q * w (y i)))) =
      ∑ i ∈ S,
        (k i * (Real.exp (-(q * ((t i : ℝ≥0) : ℝ))) *
          (X.σ ^ 2 / 2 * iteratedDeriv 2 w (y i))) +
         k i * (Real.exp (-(q * ((t i : ℝ≥0) : ℝ))) *
          (X.c * deriv w (y i) +
            (∫ z in Iio (0 : ℝ),
              SpectrallyNegativeLevy.generatorIntegrand w (y i) z ∂X.ν) -
              q * w (y i)))) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact avram_wave6_03_actual_discounted_ruin_stopped_predividend_generator_gaussian_split_all_nu
            X x D hD w C hw q T (t i) ω
    _ = (∑ i ∈ S,
        k i * (Real.exp (-(q * ((t i : ℝ≥0) : ℝ))) *
          (X.σ ^ 2 / 2 * iteratedDeriv 2 w (y i)))) +
      (∑ i ∈ S,
        k i * (Real.exp (-(q * ((t i : ℝ≥0) : ℝ))) *
          (X.c * deriv w (y i) +
            (∫ z in Iio (0 : ℝ),
              SpectrallyNegativeLevy.generatorIntegrand w (y i) z ∂X.ν) -
              q * w (y i)))) := by
          rw [Finset.sum_add_distrib]
