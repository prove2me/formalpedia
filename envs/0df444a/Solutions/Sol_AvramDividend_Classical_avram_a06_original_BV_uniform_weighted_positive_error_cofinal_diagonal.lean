-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_original_BV_uniform_weighted_positive_error_cofinal_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T14:53:19.972215+00:00
-- url     : https://prove2.me/submissions/f836913f-e726-4dd0-95d7-1a70e25b3262

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_BV_prejump_uniform_band_positive_error_L1_any_clock
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
      (∀ n, Integrable (fun ω => max (Err n (κ n) ω) 0) P) ∧
      Tendsto (fun n => (1 + L n) *
        ∫ ω, max (Err n (κ n) ω) 0 ∂P)
        atTop (𝓝 (0 : ℝ))  := by
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
  let E : ℕ → ℕ → ℝ := fun n k =>
    ∫ ω, max (Err n k ω) 0 ∂P
  have hRows (n : ℕ) :
      (∀ k, Integrable (fun ω => max (Err n k ω) 0) P) ∧
      Tendsto (fun k => E n k) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Err, E] using
      (avram_a06_original_BV_prejump_uniform_band_positive_error_L1_any_clock
        X hX hBV x C D hD T u n a b hExh)
  have hNonneg (n k : ℕ) : 0 ≤ E n k := by
    dsimp only [E]
    exact integral_nonneg (fun ω => le_max_right (Err n k ω) 0)
  obtain ⟨κ, hMono, hAbove, hLimit⟩ :=
    avram_a06_bv_cofinal_weighted_spatial_error_diagonal
      E hNonneg (fun n => (hRows n).2) L hL
  refine ⟨κ, hMono, hAbove, ?_, ?_⟩
  · exact fun n => (hRows n).1 (κ n)
  · exact hLimit
