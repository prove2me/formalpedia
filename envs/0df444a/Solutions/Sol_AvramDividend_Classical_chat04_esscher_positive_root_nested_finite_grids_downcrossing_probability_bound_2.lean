-- Prove2me | solution 2 for AvramDividend.Classical.chat04_esscher_positive_root_nested_finite_grids_downcrossing_probability_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T07:19:47.490013+00:00
-- url     : https://prove2.me/submissions/e4664c78-df3a-473b-86ac-8ff8d236946e

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Probability.Process.Filtration
import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_positive_root_finite_grid_downcrossing_probability_bound
import Theorems.Thm_AvramDividend_Classical_uniform_weighted_finite_prefix_measure_bound_extends_to_countable_union
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ b : ℝ) (hq : 0 < q) (hφ : 0 < φ)
    (hroot : X.ψ φ = q)
    (T : ℝ≥0) (g : ℕ → ℕ → ℝ≥0) (m : ℕ → ℕ)
    (hg : ∀ n : ℕ, Monotone (g n))
    (hgT : ∀ n k : ℕ, g n k ≤ T)
    (hnested : Monotone (fun n : ℕ =>
      {ω : Ω | ∃ k : ℕ, k ≤ m n ∧ X.X (g n k) ω ≤ -b}))
    (a : ℝ≥0) (ha : (a : ℝ) = Real.exp ((φ / 2) * b)) :
    (a : ℝ≥0∞) *
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (φ * X.X T ω - (T : ℝ) * X.ψ φ))))
      (⋃ n : ℕ,
        {ω : Ω | ∃ k : ℕ, k ≤ m n ∧ X.X (g n k) ω ≤ -b}) ≤ 1 := by
  let μ : Measure Ω := P.withDensity (fun ω : Ω =>
    ENNReal.ofReal (Real.exp (φ * X.X T ω - (T : ℝ) * X.ψ φ)))
  let s : ℕ → Set Ω := fun n =>
    {ω : Ω | ∃ k : ℕ, k ≤ m n ∧ X.X (g n k) ω ≤ -b}
  have hs : Monotone s := hnested
  have hms : ∀ n : ℕ, MeasurableSet (s n) := by
    intro n
    have heq : s n =
        ⋃ k : ℕ, ⋃ (_ : k ≤ m n),
          {ω : Ω | X.X (g n k) ω ≤ -b} := by
      ext ω
      simp only [s, Set.mem_setOf_eq, Set.mem_iUnion]
      constructor
      · rintro ⟨k, hk, hdown⟩
        exact ⟨k, hk, hdown⟩
      · rintro ⟨k, hk, hdown⟩
        exact ⟨k, hk, hdown⟩
    rw [heq]
    apply MeasurableSet.iUnion
    intro k
    apply MeasurableSet.iUnion
    intro hk
    have hX : Measurable (X.X (g n k)) :=
      (X.adapted (g n k)).mono (𝓕.le (g n k)) le_rfl
    exact hX measurableSet_Iic
  have hfinite : ∀ n : ℕ, (a : ℝ≥0∞) * μ (s n) ≤ 1 := by
    intro n
    exact chat04_esscher_positive_root_finite_grid_downcrossing_probability_bound
      X q φ b hq hφ hroot T (g n) (hg n)
      (hgT n) a ha (m n)
  exact uniform_weighted_finite_prefix_measure_bound_extends_to_countable_union
    μ s hs hms (a : ℝ≥0∞) hfinite
