-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB114_original_barrier_upperstrip_stopped_full_GH_mesh_equals_linear_noise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T17:21:11.773809+00:00
-- url     : https://prove2.me/submissions/657d9851-257e-493c-b9ec-db82dbbd71e9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB51_original_barrier_upperstrip_physical_GH_coefficients
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section
/-- The original upper-strip G/H source is exactly the stopped linear noise. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (ω : Ω)
    (hTube : ∀ u : ℝ≥0, u ≤ T →
      |X.X u ω| ≤ (1 / 400 : ℝ))
    (m : ℕ) (s : ℕ → ℝ≥0) (Z v : ℕ → ℝ)
    (q a : ℝ) (w : ℝ → ℝ) :
    let Y : ℕ → ℝ := fun i =>
      (1 / 8 : ℝ) + X.X (s i) ω -
        rightLimit (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) (s i) ω
    (Finset.range (m + 1)).sum (fun i =>
      (if s i < T then Real.exp (-(q * (s i : ℝ))) *
        (if Y i ∈ Icc a (5 / 44 : ℝ) then deriv w (Y i) else 1)
      else 0) * Z i +
      (if s i < T then (1 / 2 : ℝ) * Real.exp (-(q * (s i : ℝ))) *
        (if Y i ∈ Icc a (5 / 44 : ℝ) then iteratedDeriv 2 w (Y i) else 0)
      else 0) * (Z i ^ 2 - v i)) =
    (Finset.range (m + 1)).sum (fun i =>
      if s i < T then Real.exp (-(q * (s i : ℝ))) * Z i else 0)
    := by
  dsimp
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hs : s i < T
  · have hCoeff :=
      avram_gbB51_original_barrier_upperstrip_physical_GH_coefficients
        X T (s i) ω hTube hs q a w
    dsimp at hCoeff
    simp only [if_pos hs]
    rw [hCoeff.1, hCoeff.2]
    ring
  · simp [hs]
