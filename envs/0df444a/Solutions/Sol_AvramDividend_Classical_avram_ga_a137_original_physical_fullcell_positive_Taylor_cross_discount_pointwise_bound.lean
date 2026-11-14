-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a137_original_physical_fullcell_positive_Taylor_cross_discount_pointwise_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T12:00:49.449391+00:00
-- url     : https://prove2.me/submissions/5dc56455-7961-4bc2-8af3-7852c69c6c32

import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a130_original_gaussian_physically_full_mesh_three_error_source_exact_sum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

/-- Source-exact original Gaussian physical full cells have positive spatial error bounded by one-sided Taylor, absolute Gaussian Hessian cross and one-sided discount errors. -/
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
    max (∑ i ∈ Finset.range m, if cut i then F i else 0) 0 ≤
      max (∑ i ∈ Finset.range m, if cut i then T i else 0) 0 +
      |∑ i ∈ Finset.range m, if cut i then B i else 0| +
      max (∑ i ∈ Finset.range m, if cut i then C i else 0) 0 := by
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
  have hSplit := avram_ga_a130_original_gaussian_physically_full_mesh_three_error_source_exact_sum
    X hν x D w q ω n m ρ
  change (∑ i ∈ Finset.range m, if cut i then F i else 0) =
    (∑ i ∈ Finset.range m, if cut i then T i else 0) +
    (∑ i ∈ Finset.range m, if cut i then B i else 0) +
    (∑ i ∈ Finset.range m, if cut i then C i else 0) at hSplit
  change max (∑ i ∈ Finset.range m, if cut i then F i else 0) 0 ≤
    max (∑ i ∈ Finset.range m, if cut i then T i else 0) 0 +
    |∑ i ∈ Finset.range m, if cut i then B i else 0| +
    max (∑ i ∈ Finset.range m, if cut i then C i else 0) 0
  rw [hSplit]
  have hT := le_max_left (∑ i ∈ Finset.range m, if cut i then T i else 0) 0
  have hB := le_abs_self (∑ i ∈ Finset.range m, if cut i then B i else 0)
  have hC := le_max_left (∑ i ∈ Finset.range m, if cut i then C i else 0) 0
  have hT0 := le_max_right (∑ i ∈ Finset.range m, if cut i then T i else 0) 0
  have hB0 := abs_nonneg (∑ i ∈ Finset.range m, if cut i then B i else 0)
  have hC0 := le_max_right (∑ i ∈ Finset.range m, if cut i then C i else 0) 0
  exact max_le (by linarith) (by linarith)
