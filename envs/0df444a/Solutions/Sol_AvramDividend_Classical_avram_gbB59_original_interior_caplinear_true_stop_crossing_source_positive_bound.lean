-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB59_original_interior_caplinear_true_stop_crossing_source_positive_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:35:01.124956+00:00
-- url     : https://prove2.me/submissions/6046f85e-949e-4057-9324-f0167a55adce

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a147_original_true_crossing_source_value_HJB_positive_sum_envelope
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (b q : ℝ)
    (ω : Ω) (n m : ℕ) (ρ : ℝ≥0) :
    let Vb : ℝ → ℝ := fun y =>
      if y ≤ b then w y else w b + (y - b)
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
    let R : ℕ → ℝ := fun i => X.X (s i + Δ) ω - X.X (s i) ω
    let Z : ℕ → ℝ := fun i => R i - (Δ : ℝ) * X.c
    let H : ℕ → ℝ := fun i => E (s i) *
      (deriv Vb (Y (s i)) * Z i +
        (iteratedDeriv 2 Vb (Y (s i)) / 2) *
          (Z i^2 - (Δ : ℝ) * X.σ^2)) +
        (Δ : ℝ) * E (s i) * X.generator Vb (Y (s i))
    let V : ℕ → ℝ := fun i =>
      Vb (Y (s i) + (X.X ρ ω - X.X (s i) ω)) - Vb (Y (s i))
    let Ccell : ℕ → ℝ := fun i => E ρ * V i - H i
    let cut : ℕ → Prop := fun i => s i < ρ ∧ ρ < s i + Δ
    max (∑ i ∈ Finset.range m, if cut i then Ccell i else 0) 0 ≤
      ∑ i ∈ Finset.range m,
        if cut i then |E ρ| * |V i| + |H i| else 0 := by
  let Vb : ℝ → ℝ := fun y =>
    if y ≤ b then w y else w b + (y - b)
  exact avram_ga_a147_original_true_crossing_source_value_HJB_positive_sum_envelope
    X x D Vb q ω n m ρ
