-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_f_chainlimit_original_discounted_actual_source_variation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T14:53:53.738734+00:00
-- url     : https://prove2.me/submissions/75ce7f83-14fa-4f7b-beef-b1c00f4e340b

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_main_original_jump_removed_grid_variation
import Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_negative_jump_unmarked_grid_partition
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P,
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) - J t
      let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
      ∀ (n : ℕ) (u : ℕ → ℝ≥0) (q : ℝ) (hq : 0 ≤ q),
        (∀ i, i < n → u i ≤ u (i + 1)) →
        (∀ i, i < n → J (u i) ≤ J (u (i + 1))) →
        (∑ i ∈ Finset.range n,
          Real.exp (-(q * (u i : ℝ))) *
            |X.X (u (i + 1)) ω - X.X (u i) ω|) ≤
          |X.drift| * ((u n : ℝ) - (u 0 : ℝ)) +
            (R (u n) - R (u 0)) +
            (J (u n) - J (u 0)) := by
  filter_upwards
    [avram_p3_main_original_jump_removed_grid_variation X hBV]
      with ω hω
  intro J R n u q hq hGrid hJmono
  let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
  have hY := hω n u hGrid
  have hweight : ∀ i,
      0 ≤ Real.exp (-(q * (u i : ℝ))) ∧
        Real.exp (-(q * (u i : ℝ))) ≤ 1 := by
    intro i
    have hn : 0 ≤ q * (u i : ℝ) := mul_nonneg hq (u i).property
    constructor
    · exact (Real.exp_pos _).le
    · calc
        Real.exp (-(q * (u i : ℝ))) ≤ Real.exp 0 :=
          Real.exp_le_exp.mpr (neg_nonpos.mpr hn)
        _ = 1 := Real.exp_zero
  have hcell : ∀ i, i < n →
      |X.X (u (i + 1)) ω - X.X (u i) ω| ≤
        |Y (u (i + 1)) - Y (u i)| +
          (J (u (i + 1)) - J (u i)) := by
    intro i hi
    have hj : 0 ≤ J (u (i + 1)) - J (u i) :=
      sub_nonneg.mpr (hJmono i hi)
    have hsource :
        X.X (u (i + 1)) ω - X.X (u i) ω =
          (Y (u (i + 1)) - Y (u i)) -
            (J (u (i + 1)) - J (u i)) := by
      dsimp only [Y]
      ring
    rw [hsource]
    calc
      |(Y (u (i + 1)) - Y (u i)) -
          (J (u (i + 1)) - J (u i))| ≤
          |Y (u (i + 1)) - Y (u i)| +
            |J (u (i + 1)) - J (u i)| := by
              simpa [abs_sub_comm] using abs_sub_le
                (Y (u (i + 1)) - Y (u i)) 0
                (J (u (i + 1)) - J (u i))
      _ = _ := by rw [abs_of_nonneg hj]
  have htel :
      (Finset.range n).sum (fun i =>
        J (u (i + 1)) - J (u i)) =
        J (u n) - J (u 0) := by
    have hh :=
      avram_p3_f_chainlimit_original_negative_jump_unmarked_grid_partition
        X hBV u n (∅ : Finset ℕ) ω
    simpa using hh
  calc
    (∑ i ∈ Finset.range n,
      Real.exp (-(q * (u i : ℝ))) *
        |X.X (u (i + 1)) ω - X.X (u i) ω|) ≤
      ∑ i ∈ Finset.range n,
        (|Y (u (i + 1)) - Y (u i)| +
          (J (u (i + 1)) - J (u i))) := by
            apply Finset.sum_le_sum
            intro i hi
            have hle := (hweight i).2
            have ha := abs_nonneg (X.X (u (i + 1)) ω - X.X (u i) ω)
            calc
              Real.exp (-(q * (u i : ℝ))) *
                  |X.X (u (i + 1)) ω - X.X (u i) ω| ≤
                1 * |X.X (u (i + 1)) ω - X.X (u i) ω| :=
                  mul_le_mul_of_nonneg_right hle ha
              _ = _ := one_mul _
              _ ≤ _ := hcell i (Finset.mem_range.mp hi)
    _ = (∑ i ∈ Finset.range n,
          |Y (u (i + 1)) - Y (u i)|) +
        (J (u n) - J (u 0)) := by
          rw [Finset.sum_add_distrib, htel]
    _ ≤ _ := by linarith only [hY]
