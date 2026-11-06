-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_h_gaussian_original_largejump_tsum_finite_support
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:40:40.483297+00:00
-- url     : https://prove2.me/submissions/d1c8527c-3697-4068-96de-fafce4fc221d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_original_jump_test_tsum_eq_actual_finset
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical
noncomputable section

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The source large negative jumps have finite support and their time sum
is literally the finite sum on the original path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) :
    let j : ℝ≥0 → ℝ := fun u =>
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
    ∃ F : Finset ℝ≥0,
      (∀ u : ℝ≥0, u ∈ F ↔ 0 < u ∧ u ≤ T ∧ j u ≤ -1) ∧
      (∑' u : ℝ≥0,
        if 0 < u ∧ u ≤ T then (if j u ≤ -1 then j u else 0) else 0) =
        ∑ u ∈ F, j u := by
  classical
  let j : ℝ≥0 → ℝ := fun u =>
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
  have hzero : ∀ y : ℝ, |y| < 1 →
      (if y ≤ -1 then y else 0) = 0 := by
    intro y hy
    have hgt : -1 < y := (abs_lt.mp hy).1
    simp [not_le.mpr hgt]
  obtain ⟨F, hF, hsum⟩ :=
    avram_p2_h_cadlag_original_jump_test_tsum_eq_actual_finset
      X ω T (fun y : ℝ => if y ≤ -1 then y else 0) 1 (by norm_num) hzero
  have hF' : ∀ u : ℝ≥0, u ∈ F ↔
      0 < u ∧ u ≤ T ∧ j u ≤ -1 := by
    intro u
    constructor
    · intro hu
      obtain ⟨hu0, huT, hnz⟩ := (hF u).mp hu
      have hb : j u ≤ -1 := by
        by_contra hnot
        have hgt : -1 < j u := lt_of_not_ge hnot
        change (if j u ≤ -1 then j u else 0) ≠ 0 at hnz
        simp [not_le.mpr hgt] at hnz
      exact ⟨hu0, huT, hb⟩
    · intro hu
      have hne : j u ≠ 0 := by linarith [hu.2.2]
      exact (hF u).mpr ⟨hu.1, hu.2.1, by
        change (if j u ≤ -1 then j u else 0) ≠ 0
        simp [hu.2.2, hne]⟩
  change ∃ F : Finset ℝ≥0,
    (∀ u : ℝ≥0, u ∈ F ↔ 0 < u ∧ u ≤ T ∧ j u ≤ -1) ∧
    (∑' u : ℝ≥0,
      if 0 < u ∧ u ≤ T then (if j u ≤ -1 then j u else 0) else 0) =
      ∑ u ∈ F, j u
  refine ⟨F, hF', ?_⟩
  calc
    (∑' u : ℝ≥0,
      if 0 < u ∧ u ≤ T then (if j u ≤ -1 then j u else 0) else 0) =
      ∑ u ∈ F, (if j u ≤ -1 then j u else 0) := by simpa only [j] using hsum
    _ = ∑ u ∈ F, j u := by
      apply Finset.sum_congr rfl
      intro u hu
      simp [((hF' u).mp hu).2.2]
