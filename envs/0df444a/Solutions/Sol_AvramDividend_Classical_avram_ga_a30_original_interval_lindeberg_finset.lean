-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a30_original_interval_lindeberg_finset
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:37:59.185514+00:00
-- url     : https://prove2.me/submissions/b1db7bc2-b703-48ab-8679-604da3184db6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a29_original_interval_lindeberg_tail
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Sum original, measurable, deterministic-interval Gaussian large-value energy tails. -/
theorem solution
    {ι Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (I : Finset ι) (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : 0 < X.σ)
    (a b : ι → ℝ≥0) (htime : ∀ i ∈ I, a i ≤ b i)
    (hProxy : ∀ i ∈ I, Measurable (fun ω : Ω =>
      (X.X (b i - a i) ω - ((b i - a i : ℝ≥0) : ℝ) * X.c) / X.σ))
    (hZ : ∀ i ∈ I, Measurable (fun ω : Ω =>
      ((X.X (b i) ω - X.X (a i) ω) -
        ((b i - a i : ℝ≥0) : ℝ) * X.c) / X.σ))
    (r : ℝ) (hr : 0 < r) :
    let Z : ι → Ω → ℝ := fun i ω =>
      ((X.X (b i) ω - X.X (a i) ω) -
        ((b i - a i : ℝ≥0) : ℝ) * X.c) / X.σ
    (∫⁻ ω, ∑ i ∈ I,
       ENNReal.ofReal (if r ≤ |Z i ω| then (Z i ω) ^ 2 else 0) ∂P) ≤
    ∑ i ∈ I, ENNReal.ofReal (1 / r ^ 2) *
      ENNReal.ofReal (3 * (((b i - a i : ℝ≥0) : ℝ) ^ 2)) := by
  classical
  dsimp
  let Z : ι → Ω → ℝ := fun i ω =>
      ((X.X (b i) ω - X.X (a i) ω) -
        ((b i - a i : ℝ≥0) : ℝ) * X.c) / X.σ
  change (∫⁻ ω, ∑ i ∈ I,
       ENNReal.ofReal (if r ≤ |Z i ω| then (Z i ω) ^ 2 else 0) ∂P) ≤
    ∑ i ∈ I, ENNReal.ofReal (1 / r ^ 2) *
      ENNReal.ofReal (3 * (((b i - a i : ℝ≥0) : ℝ) ^ 2))
  have hE (i : ι) (hi : i ∈ I) :
      Measurable (fun ω : Ω =>
        ENNReal.ofReal (if r ≤ |Z i ω| then (Z i ω) ^ 2 else 0)) := by
    have hZi : Measurable (Z i) := hZ i hi
    have hSet : MeasurableSet {ω : Ω | r ≤ |Z i ω|} :=
      measurableSet_le measurable_const hZi.abs
    have hReal : Measurable
        (fun ω : Ω => if r ≤ |Z i ω| then (Z i ω) ^ 2 else 0) :=
      Measurable.ite hSet (hZi.pow_const 2) measurable_const
    exact ENNReal.measurable_ofReal.comp hReal
  calc
    (∫⁻ ω, ∑ i ∈ I,
      ENNReal.ofReal (if r ≤ |Z i ω| then (Z i ω) ^ 2 else 0) ∂P) =
      ∑ i ∈ I, (∫⁻ ω,
        ENNReal.ofReal (if r ≤ |Z i ω| then (Z i ω) ^ 2 else 0) ∂P) := by
          exact lintegral_finset_sum I (fun i hi => (hE i hi))
    _ ≤ ∑ i ∈ I, ENNReal.ofReal (1 / r ^ 2) *
        ENNReal.ofReal (3 * (((b i - a i : ℝ≥0) : ℝ) ^ 2)) := by
          apply Finset.sum_le_sum
          intro i hi
          simpa only [Z] using
            avram_ga_a29_original_interval_lindeberg_tail X hν hσ
            (a i) (b i) (htime i hi) (hProxy i hi) (hZ i hi) r hr
