-- Prove2me | solution 1 for AvramDividend.Classical.killed_esscher_weight_pointwise_time_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T23:07:02.603553+00:00
-- url     : https://prove2.me/submissions/2c7c5f01-e778-4ded-89ac-bad599e019c4

import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_AvramDividend_Classical_esscher_compensated_exp_time_split
import Theorems.Thm_AvramDividend_Classical_lower_survival_future_increment_pathwise_split

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

/--
The killed Esscher reward splits pointwise into its historical
survival reward and its stationary future-increment survival reward.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (x : ℝ) (s u : ℝ≥0) (ω : Ω) :
    ({ω | ∀ v : ℝ≥0, v ≤ s + u → 0 ≤ x + X.X v ω}).indicator
      (fun ω => Real.exp
        (θ * X.X (s + u) ω -
          ((s + u : ℝ≥0) : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω =
    (({ω | ∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω}).indicator
      (fun ω => Real.exp
        (θ * X.X s ω -
          (s : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω) *
    (({ω | ∀ v : ℝ≥0, v ≤ u →
        0 ≤ (x + X.X s ω) + (X.X (s + v) ω - X.X s ω)}).indicator
      (fun ω => Real.exp
        (θ * (X.X (s + u) ω - X.X s ω) -
          (u : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω) := by
  let A : Set Ω :=
    {ω | ∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω}
  let B : Set Ω :=
    {ω | ∀ v : ℝ≥0, v ≤ u →
      0 ≤ (x + X.X s ω) + (X.X (s + v) ω - X.X s ω)}
  have hSplit :
      {ω | ∀ v : ℝ≥0, v ≤ s + u → 0 ≤ x + X.X v ω} = A ∩ B :=
    lower_survival_future_increment_pathwise_split X.X x s u
  rw [hSplit]
  change (A ∩ B).indicator _ ω = A.indicator _ ω * B.indicator _ ω
  by_cases hA : ω ∈ A
  · by_cases hB : ω ∈ B
    · have hAB : ω ∈ A ∩ B := ⟨hA, hB⟩
      simp only [Set.indicator_of_mem hAB, Set.indicator_of_mem hA,
        Set.indicator_of_mem hB]
      exact esscher_compensated_exp_time_split X θ s u ω
    · have hAB : ω ∉ A ∩ B := fun h => hB h.2
      simp [Set.indicator_apply, hAB, hB]
  · have hAB : ω ∉ A ∩ B := fun h => hA h.1
    simp [Set.indicator_apply, hAB, hA]
