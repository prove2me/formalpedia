-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb27a_original_finite_mark_grid_to_real_floor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T16:37:53.865948+00:00
-- url     : https://prove2.me/submissions/0a6497e6-d9c1-4ec5-9cf8-e02be6be1eb8

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb25_uniform_cell_source_sum_as_restricted_integral
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q T : ℝ) (hT : 0 < T) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2))
    (n : ℕ) (ω : Ω) :
    let U : ℝ≥0 → ℝ := fun t => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    let ψ : ℝ → ℝ := fun b =>
      ∫ z in Set.Iio (0 : ℝ), w (b + z) - w b ∂X.ν
    let c : ℕ → ℝ := fun i =>
      if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
         0 ≤ U (u n i) ∧ ENNReal.ofReal (U (u n i)) ≤ C
      then Real.exp (-(q * (u n i : ℝ))) * ψ (U (u n i))
      else 0
    let A : ℝ := ∑ i ∈ Finset.range (n + 1),
      if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
          0 ≤ U (u n i) ∧ ENNReal.ofReal (U (u n i)) ≤ C then
        (∫ z in Set.Iio (0 : ℝ),
          Real.exp (-(q * (u n i : ℝ))) *
            (w (U (u n i) + z) - w (U (u n i))) ∂X.ν) *
        ((u n (i + 1) : ℝ) - (u n i : ℝ))
      else 0
    A = ∫ r in Set.Icc (0 : ℝ) T,
      if 0 ≤ r ∧ r < T * ((n : ℝ) + 1) / ((n : ℝ) + 2)
      then c ⌊(r / T) * ((n : ℝ) + 2)⌋₊ else 0 := by
  intro U ψ c A
  have hCell : A =
      ∑ i ∈ Finset.range (n + 1),
        c i * ((u n (i + 1) : ℝ) - (u n i : ℝ)) := by
    dsimp only [A]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [c, ψ]
    split_ifs with hm
    · simp only [integral_const_mul]
    · simp
  rw [hCell]
  exact avram_bvb25_uniform_cell_source_sum_as_restricted_integral
    T hT n u huniform c
