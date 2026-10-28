-- Prove2me | solution 1 for AvramDividend.Classical.adapted_leftContinuous_progressive_of_past_approximants
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:03:59.000021+00:00
-- url     : https://prove2.me/submissions/a95df464-d966-49ed-8b68-5982bdf519f6

import Mathlib.Probability.Process.Adapted
import Theorems.Thm_AvramDividend_Classical_stronglyProgressive_of_past_finiteRange_sample
import Theorems.Thm_AvramDividend_Classical_progressive_of_pointwise_progressive_approximants

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ) (D : ℝ≥0 → Ω → ℝ)
    (hAdapted : StronglyAdapted 𝓕 D)
    (hLeft : ∀ ω t, ContinuousWithinAt (fun s : ℝ≥0 => D s ω) (Iic t) t)
    (g : ℕ → ℝ≥0 → ℝ≥0)
    (hg_meas : ∀ n, Measurable (g n))
    (hg_past : ∀ n t, g n t ≤ t)
    (hg_finite : ∀ n T, (g n '' Iic T).Finite)
    (hg_tendsto : ∀ t, Filter.Tendsto (fun n => g n t) Filter.atTop
      (nhdsWithin t (Iic t))) :
    IsStronglyProgressive 𝓕 D := by
  apply AvramDividend.Classical.progressive_of_pointwise_progressive_approximants
    (U := fun n t ω => D (g n t) ω)
  · intro n
    exact AvramDividend.Classical.stronglyProgressive_of_past_finiteRange_sample
      𝓕 D hAdapted (g n) (hg_meas n) (hg_past n) (hg_finite n)
  · intro t ω
    exact (hLeft ω t).tendsto.comp (hg_tendsto t)
