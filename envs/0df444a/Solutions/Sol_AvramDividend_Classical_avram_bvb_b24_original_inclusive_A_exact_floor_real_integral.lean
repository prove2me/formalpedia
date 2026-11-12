-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_b24_original_inclusive_A_exact_floor_real_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T00:26:07.552533+00:00
-- url     : https://prove2.me/submissions/fca2a990-27d0-4a70-a2b8-9595ef5f4fd8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva21_uniform_frozen_grid_sum_as_real_floor_integral
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The exact original inclusive stopped A sum is the physical uniform-floor real-time integral. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q T : ℝ) (hT : 0 < T)
    (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2))
    (n : ℕ) (ω : Ω) :
    let c : ℕ → ℝ := fun i =>
      let Z : ℝ := Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
      if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
         0 ≤ Z ∧ ENNReal.ofReal Z ≤ C then
        ∫ z in Iio (0 : ℝ), Real.exp (-(q * (u n i : ℝ))) *
          (w (Z + z) - w Z) ∂X.ν
      else 0
    (∑ i ∈ Finset.range (n + 1),
      let Z : ℝ := Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
      if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
         0 ≤ Z ∧ ENNReal.ofReal Z ≤ C then
        (∫ z in Iio (0 : ℝ), Real.exp (-(q * (u n i : ℝ))) *
          (w (Z + z) - w Z) ∂X.ν) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ))
      else 0) =
    ∫ t : ℝ,
      if 0 ≤ t ∧ t < T * ((n : ℝ) + 1) / ((n : ℝ) + 2)
      then c ⌊(t / T) * ((n : ℝ) + 2)⌋₊ else 0 := by
  intro c
  have hwidth (i : ℕ) :
      (u n (i + 1) : ℝ) - (u n i : ℝ) = T / ((n : ℝ) + 2) := by
    rw [huniform n (i + 1), huniform n i]
    push_cast
    ring
  calc
    (∑ i ∈ Finset.range (n + 1),
      let Z : ℝ := Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
      if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
         0 ≤ Z ∧ ENNReal.ofReal Z ≤ C then
        (∫ z in Iio (0 : ℝ), Real.exp (-(q * (u n i : ℝ))) *
          (w (Z + z) - w Z) ∂X.ν) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ))
      else 0) =
      ∑ i ∈ Finset.range (n + 1), (T / ((n : ℝ) + 2)) * c i := by
        apply Finset.sum_congr rfl
        intro i hi
        dsimp only [c]
        rw [hwidth i]
        split_ifs <;> ring
    _ = ∫ t : ℝ,
      if 0 ≤ t ∧ t < T * ((n : ℝ) + 1) / ((n : ℝ) + 2)
      then c ⌊(t / T) * ((n : ℝ) + 2)⌋₊ else 0 :=
        avram_bva21_uniform_frozen_grid_sum_as_real_floor_integral T hT n c
