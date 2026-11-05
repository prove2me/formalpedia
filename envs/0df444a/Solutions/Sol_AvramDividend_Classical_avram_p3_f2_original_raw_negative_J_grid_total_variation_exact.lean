-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_f2_original_raw_negative_J_grid_total_variation_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T22:21:47.139816+00:00
-- url     : https://prove2.me/submissions/1be4840a-e1c3-4e4c-a569-3a0b08b1ac8a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_jump_cumulative_monotone
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The actual negative raw Lévy jump mass has exact physical-grid total variation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P,
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω else 0
      ∀ (u : ℕ → ℝ≥0) (n : ℕ),
        (∀ i, i < n → u i ≤ u (i + 1)) →
        (∑ i ∈ Finset.range n,
          |J (u (i + 1)) - J (u i)|) =
        J (u n) - J (u 0) := by
  filter_upwards
    [avram_p3_a_bvdrift_original_raw_jump_cumulative_monotone X hBV]
      with ω hMono
  intro J u n hGrid
  have hStep : ∀ i, i < n →
      |J (u (i + 1)) - J (u i)| =
        J (u (i + 1)) - J (u i) := by
    intro i hi
    exact abs_of_nonneg (sub_nonneg.mpr (hMono (hGrid i hi)))
  have hTelescope (g : ℕ → ℝ) (m : ℕ) :
      (∑ k ∈ Finset.range m, (g (k + 1) - g k)) = g m - g 0 := by
    induction m with
    | zero => simp
    | succ k ih =>
        rw [Finset.sum_range_succ, ih]
        ring
  calc
    (∑ i ∈ Finset.range n,
      |J (u (i + 1)) - J (u i)|) =
      ∑ i ∈ Finset.range n,
        (J (u (i + 1)) - J (u i)) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hStep i (Finset.mem_range.mp hi)
    _ = J (u n) - J (u 0) := hTelescope (fun k => J (u k)) n
