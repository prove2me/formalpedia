-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_annulus14_original_pathwise_grid_factorial_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T10:34:29.959197+00:00
-- url     : https://prove2.me/submissions/217e59da-219b-4425-9f61-9e6cfbfda195

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_mix_annulus14_original_window_filter_card
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_run1640_original_marked_count_grid_telescoping
import Theorems.Thm_AvramDividend_Classical_avram_mixed_source13_finite_grid_factorial_collision_sandwich
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The original physical annulus factorial lies between cross-cell and full-band collision counts. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0)
    (n m : ℕ) (hnm : n ≤ m)
    (grid : ℕ → ℝ≥0) (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (hZero : grid 0 = 0) (q : ℕ) (hT : grid q = T) :
    let F : Finset ℝ≥0 :=
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T m).toFinset
    let a : ℕ → ℕ := fun i =>
      (F.filter (fun u => grid i < u ∧ u ≤ grid (i + 1) ∧
        -(1 / ((n : ℝ) + 1)) <
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)).card
    let b : ℕ → ℕ := fun i =>
      (F.filter (fun u => grid i < u ∧ u ≤ grid (i + 1))).card
    let B : Set ℝ := Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
    let N : ℝ := (((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)).toReal
    let H : ℝ := 2 * (∑ i ∈ Finset.range q,
      (∑ j ∈ Finset.range i, (a j : ℝ)) * (a i : ℝ))
    H ≤ N * (N - 1) ∧
      N * (N - 1) ≤ H +
        ∑ i ∈ Finset.range q, (b i : ℝ) * ((b i : ℝ) - 1) := by
  classical
  let F : Finset ℝ≥0 :=
    (avram_wave7_06_original_negative_band_marked_times_finite X ω T m).toFinset
  let a : ℕ → ℕ := fun i =>
    (F.filter (fun u => grid i < u ∧ u ≤ grid (i + 1) ∧
      -(1 / ((n : ℝ) + 1)) <
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)).card
  let b : ℕ → ℕ := fun i =>
    (F.filter (fun u => grid i < u ∧ u ≤ grid (i + 1))).card
  let B : Set ℝ := Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
  let J : ℝ≥0 → ℝ≥0 → ℝ≥0∞ := fun s t =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ B)
  let N : ℝ := (J 0 T).toReal
  let H : ℝ := 2 * (∑ i ∈ Finset.range q,
    (∑ j ∈ Finset.range i, (a j : ℝ)) * (a i : ℝ))
  change H ≤ N * (N - 1) ∧
    N * (N - 1) ≤ H +
      ∑ i ∈ Finset.range q, (b i : ℝ) * ((b i : ℝ) - 1)
  have hMono : Monotone grid := monotone_nat_of_le_succ hGrid
  have hEnd (i : ℕ) (hi : i < q) : grid (i + 1) ≤ T := by
    rw [← hT]
    exact hMono (Nat.succ_le_of_lt hi)
  have hCell (i : ℕ) (hi : i < q) :
      J (grid i) (grid (i + 1)) = (a i : ℝ≥0∞) := by
    exact avram_mix_annulus14_original_window_filter_card
      X ω (grid i) (grid (i + 1)) T (hGrid i) (hEnd i hi) n m hnm
  have hTel :=
    avram_p4_s3_run1640_original_marked_count_grid_telescoping
      X ω grid hGrid hZero B measurableSet_Ioc q
  change (∑ i ∈ Finset.range q, J (grid i) (grid (i + 1))) =
    J 0 (grid q) at hTel
  have hSum :
      (∑ i ∈ Finset.range q, (a i : ℝ≥0∞)) = J 0 T := by
    calc
      _ = ∑ i ∈ Finset.range q, J (grid i) (grid (i + 1)) := by
        exact Finset.sum_congr rfl
          (fun i hi => (hCell i (Finset.mem_range.mp hi)).symm)
      _ = J 0 (grid q) := hTel
      _ = J 0 T := by rw [hT]
  have hN : N = ∑ i ∈ Finset.range q, (a i : ℝ) := by
    have h := congrArg ENNReal.toReal hSum.symm
    change (J 0 T).toReal =
      (∑ i ∈ Finset.range q, (a i : ℝ≥0∞)).toReal at h
    have hRealCast :
        (∑ i ∈ Finset.range q, (a i : ℝ≥0∞)).toReal =
          ∑ i ∈ Finset.range q, (a i : ℝ) := by
      simpa only [ENNReal.toReal_natCast] using
        (ENNReal.toReal_sum (s := Finset.range q)
          (f := fun i : ℕ => (a i : ℝ≥0∞))
          (by intro i hi; simp))
    exact h.trans hRealCast
  have hab (i : ℕ) : a i ≤ b i := by
    dsimp [a, b]
    apply Finset.card_le_card
    intro u hu
    simp only [Finset.mem_filter] at hu ⊢
    exact ⟨hu.1, hu.2.1, hu.2.2.1⟩
  have hDet :=
    avram_mixed_source13_finite_grid_factorial_collision_sandwich q a b hab
  change H ≤
      (∑ i ∈ Finset.range q, (a i : ℝ)) *
        ((∑ i ∈ Finset.range q, (a i : ℝ)) - 1) ∧
    (∑ i ∈ Finset.range q, (a i : ℝ)) *
        ((∑ i ∈ Finset.range q, (a i : ℝ)) - 1) ≤
      H + (∑ i ∈ Finset.range q, (b i : ℝ) * ((b i : ℝ) - 1))
    at hDet
  rw [← hN] at hDet
  exact hDet
