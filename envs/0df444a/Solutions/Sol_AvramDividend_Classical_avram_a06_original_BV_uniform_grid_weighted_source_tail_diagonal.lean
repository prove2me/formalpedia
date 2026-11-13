-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_original_BV_uniform_grid_weighted_source_tail_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T14:40:48.540519+00:00
-- url     : https://prove2.me/submissions/354ad6e2-23aa-4f05-a5c7-7031ae3fd870

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_BV_prejump_uniform_band_source_mass_L1_tail_any_clock
import Theorems.Thm_AvramDividend_Classical_avram_p3_comp8_original_BV_source_mass_integrable_any_clock
import Theorems.Thm_AvramDividend_Classical_avram_a06_bv_cofinal_weighted_spatial_error_diagonal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology Classical
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ≥0) (u : ℕ → ℕ → ℝ≥0) (a b : ℕ → ℝ)
    (hExh : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      ∃ N : ℕ, ∀ k ≥ N, y ∈ Icc (a k) (b k))
    (L : ℕ → ℝ) (hL : ∀ n, 0 ≤ L n) :
    let E : ℕ → ℕ → ℝ := fun n k =>
      ∫ ω, (if ∀ i < n + 1,
        (0 < Function.leftLim
          (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) (u n i) ∧
          ENNReal.ofReal (Function.leftLim
          (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) (u n i)) < C) →
        Function.leftLim
          (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) (u n i)
            ∈ Icc (a k) (b k) then (0 : ℝ)
          else |X.drift| * (T : ℝ) +
            |(T : ℝ) * X.drift - X.X T ω|) ∂P
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ n, n ≤ φ n) ∧
      Tendsto (fun n => (1 + L n) * E n (φ n)) atTop (𝓝 (0 : ℝ))  := by
  let E : ℕ → ℕ → ℝ := fun n k =>
    ∫ ω, (if ∀ i < n + 1,
      (0 < Function.leftLim
        (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) (u n i) ∧
        ENNReal.ofReal (Function.leftLim
        (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) (u n i)) < C) →
      Function.leftLim
        (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) (u n i)
          ∈ Icc (a k) (b k) then (0 : ℝ)
        else |X.drift| * (T : ℝ) +
          |(T : ℝ) * X.drift - X.X T ω|) ∂P
  have hSourceNonneg (ω : Ω) :
      0 ≤ |X.drift| * (T : ℝ) + |(T : ℝ) * X.drift - X.X T ω| :=
    (avram_p3_comp8_original_BV_source_mass_integrable_any_clock
      X hX hBV T).2 ω
  have hNonneg (n k : ℕ) : 0 ≤ E n k := by
    dsimp [E]
    apply integral_nonneg
    intro ω
    dsimp
    split_ifs
    · exact le_rfl
    · exact hSourceNonneg ω
  have hVanish (n : ℕ) :
      Tendsto (fun k => E n k) atTop (𝓝 (0 : ℝ)) := by
    simpa only [E] using
      (avram_a06_original_BV_prejump_uniform_band_source_mass_L1_tail_any_clock
        X hX hBV x C D hD T u n a b hExh)
  simpa only [E] using
    (avram_a06_bv_cofinal_weighted_spatial_error_diagonal
      E hNonneg hVanish L hL)
