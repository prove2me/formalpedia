-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a130_original_gaussian_physically_full_mesh_three_error_source_exact_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T11:21:30.33703+00:00
-- url     : https://prove2.me/submissions/256704ef-370c-4e38-8998-8a8cfdeecf63

import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a128_original_gaussian_physical_source_full_cell_three_error_exact_algebra
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

/-- Original Gaussian pre-stop fully physical cells decompose into three exact source-error sums, reusing the proved pointwise identity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ)
    (q : ℝ) (ω : Ω) (n m : ℕ) (ρ : ℝ≥0) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℕ → ℝ := fun i => x + X.X (s i) ω - rightLimit D (s i) ω
    let R : ℕ → ℝ := fun i => X.X (s i + Δ) ω - X.X (s i) ω
    let Z : ℕ → ℝ := fun i => R i - (Δ : ℝ) * X.c
    let H : ℕ → ℝ := fun i => E (s i) *
      (deriv w (Y i) * Z i + (iteratedDeriv 2 w (Y i) / 2) *
        (Z i^2 - (Δ : ℝ) * X.σ^2)) +
      (Δ : ℝ) * E (s i) * X.generator w (Y i)
    let F : ℕ → ℝ := fun i =>
      E (s i + Δ) * (w (Y i + R i) - w (Y i)) - H i
    let T : ℕ → ℝ := fun i => E (s i) *
      (w (Y i + R i) - w (Y i) - deriv w (Y i) * R i -
        (iteratedDeriv 2 w (Y i) / 2) * R i^2)
    let B : ℕ → ℝ := fun i => E (s i) *
      (iteratedDeriv 2 w (Y i) / 2) * (R i^2 - Z i^2)
    let C : ℕ → ℝ := fun i =>
      (E (s i + Δ) - E (s i)) * (w (Y i + R i) - w (Y i))
    let cut : ℕ → Prop := fun i => s i < ρ ∧ s i + Δ ≤ ρ
    (∑ i ∈ Finset.range m, if cut i then F i else 0) =
      (∑ i ∈ Finset.range m, if cut i then T i else 0) +
      (∑ i ∈ Finset.range m, if cut i then B i else 0) +
      (∑ i ∈ Finset.range m, if cut i then C i else 0) := by
  classical
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
  let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
  let Y : ℕ → ℝ := fun i => x + X.X (s i) ω - rightLimit D (s i) ω
  let R : ℕ → ℝ := fun i => X.X (s i + Δ) ω - X.X (s i) ω
  let Z : ℕ → ℝ := fun i => R i - (Δ : ℝ) * X.c
  let H : ℕ → ℝ := fun i => E (s i) *
    (deriv w (Y i) * Z i + (iteratedDeriv 2 w (Y i) / 2) *
      (Z i^2 - (Δ : ℝ) * X.σ^2)) +
    (Δ : ℝ) * E (s i) * X.generator w (Y i)
  let F : ℕ → ℝ := fun i =>
    E (s i + Δ) * (w (Y i + R i) - w (Y i)) - H i
  let T : ℕ → ℝ := fun i => E (s i) *
    (w (Y i + R i) - w (Y i) - deriv w (Y i) * R i -
      (iteratedDeriv 2 w (Y i) / 2) * R i^2)
  let B : ℕ → ℝ := fun i => E (s i) *
    (iteratedDeriv 2 w (Y i) / 2) * (R i^2 - Z i^2)
  let C : ℕ → ℝ := fun i =>
    (E (s i + Δ) - E (s i)) * (w (Y i + R i) - w (Y i))
  let cut : ℕ → Prop := fun i => s i < ρ ∧ s i + Δ ≤ ρ
  change (∑ i ∈ Finset.range m, if cut i then F i else 0) =
    (∑ i ∈ Finset.range m, if cut i then T i else 0) +
    (∑ i ∈ Finset.range m, if cut i then B i else 0) +
    (∑ i ∈ Finset.range m, if cut i then C i else 0)
  have hCell (i : ℕ) : F i = T i + B i + C i := by
    have h := avram_ga_a128_original_gaussian_physical_source_full_cell_three_error_exact_algebra
      X hν x D w q ω (s i) Δ
    dsimp only [F, H, T, B, C, Y, R, Z, E] at *
    convert h using 1 <;> ring
  calc
    (∑ i ∈ Finset.range m, if cut i then F i else 0) =
      ∑ i ∈ Finset.range m,
        ((if cut i then T i else 0) +
          (if cut i then B i else 0) +
          (if cut i then C i else 0)) := by
        apply Finset.sum_congr rfl
        intro i hi
        by_cases hc : cut i
        · simp only [if_pos hc, hCell i]
        · simp only [if_neg hc]; ring
    _ = (∑ i ∈ Finset.range m, if cut i then T i else 0) +
        (∑ i ∈ Finset.range m, if cut i then B i else 0) +
        (∑ i ∈ Finset.range m, if cut i then C i else 0) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
