-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva65_original_BV_diagonal_spatial_band_remains_cofinal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T16:12:02.491221+00:00
-- url     : https://prove2.me/submissions/66057668-9848-4d37-83a2-f4c79709e1bb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_BV_uniform_positive_error_cofinal_diagonal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ≥0) (u : ℕ → ℕ → ℝ≥0) (a b : ℕ → ℝ)
    (hExh : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      ∃ N : ℕ, ∀ k ≥ N, y ∈ Icc (a k) (b k)) :
    let Err : ℕ → ℕ → Ω → ℝ := fun n k ω =>
      if ∀ i < n + 1,
        (0 < Function.leftLim
          (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) (u n i) ∧
          ENNReal.ofReal (Function.leftLim
          (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) (u n i)) < C) →
        Function.leftLim
          (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) (u n i)
            ∈ Icc (a k) (b k) then (0 : ℝ)
          else |X.drift| * (T : ℝ) +
            |(T : ℝ) * X.drift - X.X T ω|
    ∃ κ : ℕ → ℕ, StrictMono κ ∧ (∀ n, n ≤ κ n) ∧
      (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → ∃ N : ℕ, ∀ n ≥ N, y ∈ Icc (a (κ n)) (b (κ n))) ∧
    (∀ n, Integrable (fun ω => max (Err n (κ n) ω) 0) P) ∧
      Tendsto (fun n => ∫ ω, max (Err n (κ n) ω) 0 ∂P)
        atTop (𝓝 (0 : ℝ)) := by
  dsimp only
  obtain ⟨κ, hMono, hAbove, hInt, hZero⟩ :=
    avram_a06_original_BV_uniform_positive_error_cofinal_diagonal
      X hX hBV x C D hD T u a b hExh
  refine ⟨κ, hMono, hAbove, ?_, hInt, hZero⟩
  intro y hy hyC
  obtain ⟨N, hN⟩ := hExh y hy hyC
  refine ⟨N, ?_⟩
  intro n hn
  exact hN (κ n) (le_trans hn (hAbove n))

