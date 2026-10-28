-- Prove2me | solution 1 for AvramDividend.Classical.chat04_esscher_positive_root_countable_monotone_grid_downcrossing_probability_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T07:23:31.716092+00:00
-- url     : https://prove2.me/submissions/0fbfcb7b-6634-4c5d-ac0e-b50673a52005

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
    (T : ℝ≥0) (g : ℕ → ℝ≥0) (hg : Monotone g)
    (hgT : ∀ k : ℕ, g k ≤ T)
    (a : ℝ≥0) (ha : (a : ℝ) = Real.exp ((φ / 2) * b)) :
    (a : ℝ≥0∞) *
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (φ * X.X T ω - (T : ℝ) * X.ψ φ))))
        {ω : Ω | ∃ k : ℕ, X.X (g k) ω ≤ -b} ≤ 1 := by
  let μ : Measure Ω :=
    P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (φ * X.X T ω - (T : ℝ) * X.ψ φ)))
  let s : ℕ → Set Ω := fun n =>
    {ω : Ω | ∃ k : ℕ, k ≤ n ∧ X.X (g k) ω ≤ -b}
  have hmono : Monotone s := by
    intro i j hij ω hω
    obtain ⟨k, hk, hdown⟩ := hω
    exact ⟨k, le_trans hk hij, hdown⟩
  have hmeas : ∀ n : ℕ, MeasurableSet (s n) := by
    intro n
    have heq : s n =
        ⋃ k : ℕ, ⋃ (_ : k ≤ n), {ω : Ω | X.X (g k) ω ≤ -b} := by
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
    have hm : Measurable (X.X (g k)) :=
      (X.adapted (g k)).mono (𝓕.le (g k)) le_rfl
    exact hm measurableSet_Iic
  have hfinite : ∀ n : ℕ, (a : ℝ≥0∞) * μ (s n) ≤ 1 := by
    intro n
    exact chat04_esscher_positive_root_finite_grid_downcrossing_probability_bound
      X q φ b hq hφ hroot T g hg hgT a ha n
  have hlim := uniform_weighted_finite_prefix_measure_bound_extends_to_countable_union
    μ s hmono hmeas (a : ℝ≥0∞) hfinite
  have heq : (⋃ n, s n) =
      {ω : Ω | ∃ k : ℕ, X.X (g k) ω ≤ -b} := by
    ext ω
    constructor
    · intro hw
      rcases Set.mem_iUnion.mp hw with ⟨n, k, hk, hdown⟩
      exact ⟨k, hdown⟩
    · rintro ⟨k, hdown⟩
      exact Set.mem_iUnion.mpr ⟨k, k, le_rfl, hdown⟩
  simpa only [μ, heq] using hlim
