-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a147_original_true_crossing_source_value_HJB_positive_sum_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T12:21:41.452185+00:00
-- url     : https://prove2.me/submissions/f8c47c02-0105-4fee-9d5b-c2c81ad309b0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a25_finite_sum_positive_part_le
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

/-- Source-exact original Gaussian genuine crossing-cell spatial positive residual has the stopped-source value-plus-full-HJB envelope. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (ω : Ω) (n m : ℕ) (ρ : ℝ≥0) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
    let R : ℕ → ℝ := fun i => X.X (s i + Δ) ω - X.X (s i) ω
    let Z : ℕ → ℝ := fun i => R i - (Δ : ℝ) * X.c
    let H : ℕ → ℝ := fun i => E (s i) *
      (deriv w (Y (s i)) * Z i +
        (iteratedDeriv 2 w (Y (s i)) / 2) *
          (Z i^2 - (Δ : ℝ) * X.σ^2)) +
        (Δ : ℝ) * E (s i) * X.generator w (Y (s i))
    let V : ℕ → ℝ := fun i =>
      w (Y (s i) + (X.X ρ ω - X.X (s i) ω)) - w (Y (s i))
    let Ccell : ℕ → ℝ := fun i => E ρ * V i - H i
    let cut : ℕ → Prop := fun i => s i < ρ ∧ ρ < s i + Δ
    max (∑ i ∈ Finset.range m, if cut i then Ccell i else 0) 0 ≤
      ∑ i ∈ Finset.range m,
        if cut i then |E ρ| * |V i| + |H i| else 0 := by
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
  let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
  let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
  let R : ℕ → ℝ := fun i => X.X (s i + Δ) ω - X.X (s i) ω
  let Z : ℕ → ℝ := fun i => R i - (Δ : ℝ) * X.c
  let H : ℕ → ℝ := fun i => E (s i) *
    (deriv w (Y (s i)) * Z i +
      (iteratedDeriv 2 w (Y (s i)) / 2) *
        (Z i^2 - (Δ : ℝ) * X.σ^2)) +
      (Δ : ℝ) * E (s i) * X.generator w (Y (s i))
  let V : ℕ → ℝ := fun i =>
    w (Y (s i) + (X.X ρ ω - X.X (s i) ω)) - w (Y (s i))
  let Ccell : ℕ → ℝ := fun i => E ρ * V i - H i
  let cut : ℕ → Prop := fun i => s i < ρ ∧ ρ < s i + Δ
  have hCell (i : ℕ) : max (Ccell i) 0 ≤
      |E ρ| * |V i| + |H i| := by
    dsimp only [Ccell]
    have h1 := le_abs_self (E ρ * V i - H i)
    have h2 := (abs_sub (E ρ * V i) (H i))
    rw [abs_mul] at h2
    exact max_le (by linarith) (by positivity)
  have hSum := avram_ga_a25_finite_sum_positive_part_le
    (Finset.range m) (fun i => if cut i then Ccell i else 0)
  change max (∑ i ∈ Finset.range m, if cut i then Ccell i else 0) 0 ≤
      ∑ i ∈ Finset.range m,
        if cut i then |E ρ| * |V i| + |H i| else 0
  calc
    max (∑ i ∈ Finset.range m, if cut i then Ccell i else 0) 0 ≤
        ∑ i ∈ Finset.range m,
          max (if cut i then Ccell i else 0) 0 := hSum
    _ ≤ ∑ i ∈ Finset.range m,
          if cut i then |E ρ| * |V i| + |H i| else 0 := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hc : cut i
      · simpa only [if_pos hc] using hCell i
      · simp only [if_neg hc, max_self, le_refl]
