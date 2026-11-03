-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_01_original_predictable_simple_marked_grid_count_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T07:06:34.194246+00:00
-- url     : https://prove2.me/submissions/b851b319-6f91-4a65-8e17-1809c97f1184

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_past_marked_grid_count_mean_factorisation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
attribute [local instance] Classical.propDecidable

/-- Finite unit-coefficient predictable simple marked grid sums for the source process. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (m : ℕ) (s : Fin m → ℝ≥0)
    (t : Fin m → ℕ → ℝ≥0)
    (ht : ∀ k, Monotone (t k))
    (hst : ∀ k, s k ≤ t k 0)
    (n : Fin m → ℕ)
    (A : Fin m → Set Ω)
    (hA : ∀ k, MeasurableSet[𝓕 (s k)] (A k))
    (B : Fin m → Set ℝ)
    (hB : ∀ k, MeasurableSet (B k)) :
    (∫⁻ ω, ∑ k : Fin m,
      (A k).indicator (fun _ => (1 : ℝ≥0∞)) ω *
      (∑ i ∈ Finset.range (n k),
        ({v : Ω | X.X (t k (i + 1)) v - X.X (t k i) v ∈ B k}).indicator
          (fun _ => (1 : ℝ≥0∞)) ω) ∂P) =
    ∑ k : Fin m, P (A k) *
      (∑ i ∈ Finset.range (n k),
        P {ω | X.X (t k (i + 1)) ω - X.X (t k i) ω ∈ B k}) := by
  classical
  let Y : Fin m → Ω → ℝ≥0∞ := fun k ω =>
    (A k).indicator (fun _ => (1 : ℝ≥0∞)) ω *
      (∑ i ∈ Finset.range (n k),
        ({v : Ω | X.X (t k (i + 1)) v - X.X (t k i) v ∈ B k}).indicator
          (fun _ => (1 : ℝ≥0∞)) ω)
  have hXm (u : ℝ≥0) : Measurable (X.X u) :=
    (X.adapted u).mono (𝓕.le u) le_rfl
  have hY (k : Fin m) : Measurable (Y k) := by
    dsimp [Y]
    apply Measurable.mul
    · exact measurable_const.indicator ((𝓕.le (s k)) _ (hA k))
    · apply Finset.measurable_sum
      intro i hi
      exact measurable_const.indicator
        ((hB k).preimage ((hXm _).sub (hXm _)))
  change (∫⁻ ω, ∑ k : Fin m, Y k ω ∂P) =
    ∑ k : Fin m, P (A k) *
      (∑ i ∈ Finset.range (n k),
        P {ω | X.X (t k (i + 1)) ω - X.X (t k i) ω ∈ B k})
  calc
    (∫⁻ ω, ∑ k : Fin m, Y k ω ∂P) =
        ∑ k : Fin m, ∫⁻ ω, Y k ω ∂P := by
          apply MeasureTheory.lintegral_finset_sum
          intro k hk
          exact hY k
    _ = ∑ k : Fin m, P (A k) *
        (∑ i ∈ Finset.range (n k),
          P {ω | X.X (t k (i + 1)) ω - X.X (t k i) ω ∈ B k}) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact avram_wave6_01_original_past_marked_grid_count_mean_factorisation
        X (s k) (t k) (ht k) (hst k) (n k) (A k) (hA k) (B k) (hB k)
