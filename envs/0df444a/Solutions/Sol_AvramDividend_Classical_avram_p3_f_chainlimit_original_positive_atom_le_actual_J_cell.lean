-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_f_chainlimit_original_positive_atom_le_actual_J_cell
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T13:29:29.373807+00:00
-- url     : https://prove2.me/submissions/ccfdc38d-3f70-47e2-b8ac-f5aacdd3ff37

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_jump_cumulative_disjoint_interval_additivity
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_raw_negative_jump_real_tsum
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_left_jump_nonnegative_and_toReal
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
        ∑' z : ℝ≥0, if 0 < z ∧ z ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) z - X.X z ω
        else 0
      ∀ s t v : ℝ≥0, s < v → v ≤ t →
        Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω ≤
          J t - J s := by
  filter_upwards
    [avram_p3_a_bvdrift_original_interval_raw_negative_jump_real_tsum X hBV,
      avram_p3_a_bvdrift_original_raw_jump_cumulative_disjoint_interval_additivity X hBV]
    with ω hsum hsplit
  intro J s t v hsv hvt
  have hst : s ≤ t := le_trans (le_of_lt hsv) hvt
  let f : ℝ≥0 → ℝ := fun z =>
    if s < z ∧ z ≤ t then
      Function.leftLim (fun r : ℝ≥0 => X.X r ω) z - X.X z ω
    else 0
  have hf : Summable f := (hsum s t hst).1
  have hp (z : ℝ≥0) : 0 ≤ f z := by
    dsimp [f]
    split_ifs with hz
    · have hs0 : (0 : ℝ≥0) ≤ s := zero_le
      exact (avram_p3_a_bvdrift_original_raw_left_jump_nonnegative_and_toReal
        X ω z (lt_of_le_of_lt hs0 hz.1)).1
    · exact le_rfl
  have hpoint (z : ℝ≥0) :
      (if z = v then f z else 0) ≤ f z := by
    by_cases hz : z = v
    · simp [hz]
    · simpa [hz] using hp z
  have hnonneg (z : ℝ≥0) :
      0 ≤ (if z = v then f z else 0) := by
    by_cases hz : z = v
    · simpa only [if_pos hz] using hp z
    · simp [hz]
  have hg : Summable (fun z : ℝ≥0 => if z = v then f z else 0) :=
    Summable.of_nonneg_of_le hnonneg hpoint hf
  have hsingle :
      (∑' z : ℝ≥0, if z = v then f z else 0) = f v := by
    simp
  have hinterval : J t - J s = ∑' z : ℝ≥0, f z := by
    have h := hsplit s t hst
    change J t = J s + ∑' z : ℝ≥0, f z at h
    linarith
  calc
    Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω =
        f v := by simp [f, hsv, hvt]
    _ = (∑' z : ℝ≥0, if z = v then f z else 0) := hsingle.symm
    _ ≤ ∑' z : ℝ≥0, f z :=
      Summable.tsum_le_tsum hpoint hg hf
    _ = J t - J s := hinterval.symm
