-- Prove2me | solution 1 for AvramDividend.Classical.avram_b254_original_ruinclipped_physical_postpayment_discount_gap_automatic_width
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T21:47:20.528903+00:00
-- url     : https://prove2.me/submissions/5193c0ef-776a-4b9b-920d-0d689dc7bd4b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_b249_original_ruinclipped_physical_postpayment_discount_gap_bounded_dividend_mass
import Theorems.Thm_AvramDividend_Classical_avram_b250_original_ruinclipped_true_physical_stopped_cell_width_and_clock_monotone
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (a b : ℝ) (hLip :
      ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
        |w s - w t| ≤ L * |s - t|)
    (σ : Ω → ℝ≥0) (n m : ℕ)
    (hPre : ∀ i < m,
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun j =>
        min ((j : ℝ≥0) * Δ) (σ ω)
      x + X.X (v (i + 1)) ω - rightLimit D (v i) ω ∈ Icc a b)
    (hPost : ∀ i < m,
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun j =>
        min ((j : ℝ≥0) * Δ) (σ ω)
      x + X.X (v (i + 1)) ω - rightLimit D (v (i + 1)) ω ∈ Icc a b) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun i =>
      min ((i : ℝ≥0) * Δ) (σ ω)
    (∑ i ∈ Finset.range m,
      (Real.exp (-(q * (v i : ℝ))) -
       Real.exp (-(q * (v (i + 1) : ℝ)))) *
      |w (x + X.X (v (i + 1)) ω - rightLimit D (v i) ω) -
       w (x + X.X (v (i + 1)) ω - rightLimit D (v (i + 1)) ω)|) ≤
    q * (Δ : ℝ) * L *
      (rightLimit D (v m) ω - rightLimit D (v 0) ω) := by
  have hmesh : ∀ i < m,
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun j =>
        min ((j : ℝ≥0) * Δ) (σ ω)
      ((v (i + 1) : ℝ) - (v i : ℝ)) ≤ (Δ : ℝ) := by
    intro i hi
    exact (avram_b250_original_ruinclipped_true_physical_stopped_cell_width_and_clock_monotone
      n m (σ ω) i).2
  exact avram_b249_original_ruinclipped_physical_postpayment_discount_gap_bounded_dividend_mass
    X x D hD ω q hq w L hL a b hLip
    σ n m hmesh hPre hPost
