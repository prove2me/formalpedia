-- Prove2me | solution 1 for AvramDividend.Classical.chat04_esscher_positive_root_nested_finite_grids_downcrossing_probability_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T07:17:59.712461+00:00
-- url     : https://prove2.me/submissions/52cbca39-b444-44de-94e2-70563a83270d

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Probability.Process.Filtration
import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_positive_root_finite_grid_downcrossing_probability_bound
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
  rw [hnested.measure_iUnion, ENNReal.mul_iSup]
  exact iSup_le fun n =>
    chat04_esscher_positive_root_finite_grid_downcrossing_probability_bound X q φ b hq hφ hroot T
      (g n) (hg n) (hgT n) a ha (m n)
