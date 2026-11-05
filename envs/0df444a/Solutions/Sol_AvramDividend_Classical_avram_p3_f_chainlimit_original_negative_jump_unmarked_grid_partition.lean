-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_f_chainlimit_original_negative_jump_unmarked_grid_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T13:17:05.447582+00:00
-- url     : https://prove2.me/submissions/1a8abfd8-0839-4b56-b312-4e3eb931b790

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (u : ℕ → ℝ≥0) (n : ℕ) (S : Finset ℕ) :
    ∀ ω,
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' s : ℝ≥0, if 0 < s ∧ s ≤ t then
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) s - X.X s ω
        else 0
      let j : ℕ → ℝ := fun i => J (u (i + 1)) - J (u i)
      (∑ i ∈ Finset.range n, if i ∈ S then 0 else j i) +
        (∑ i ∈ Finset.range n, if i ∈ S then j i else 0) =
      J (u n) - J (u 0) := by
  intro ω J j
  have htel : ∀ m : ℕ,
      (∑ i ∈ Finset.range m, j i) = J (u m) - J (u 0) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [Finset.sum_range_succ, ih]
        change J (u m) - J (u 0) +
          (J (u (m + 1)) - J (u m)) =
          J (u (m + 1)) - J (u 0)
        ring
  have hpart :
      (∑ i ∈ Finset.range n, if i ∈ S then 0 else j i) +
        (∑ i ∈ Finset.range n, if i ∈ S then j i else 0) =
      (∑ i ∈ Finset.range n, j i) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases his : i ∈ S <;> simp [his]
  exact hpart.trans (htel n)
