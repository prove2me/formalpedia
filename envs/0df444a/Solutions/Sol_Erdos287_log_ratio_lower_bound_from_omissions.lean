-- Prove2me | solution 1 for Erdos287.log_ratio_lower_bound_from_omissions
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T05:46:20.469996+00:00
-- url     : https://prove2.me/submissions/50d6d422-ed8d-4428-909b-6ee5750dadf2

import Mathlib

open Finset MeasureTheory

set_option autoImplicit false

/-- Any known omitted reciprocal mass increases the required ratio of the
maximum denominator to one less than the minimum. -/
theorem solution (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hmin : 1 < f 0)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (H : Finset ℕ)
    (hH : ∀ n ∈ H, f 0 ≤ n ∧ n ≤ f (k - 1))
    (hmiss : ∀ i, i < k → f i ∉ H) :
    (1 : ℝ) + ∑ n ∈ H, (1 : ℝ) / n ≤
      Real.log ((f (k - 1) : ℝ) / ((f 0 - 1 : ℕ) : ℝ)) := by
  classical
  let x := f 0 - 1
  let M := f (k - 1)
  let D := (range k).image f
  change (1 : ℝ) + ∑ n ∈ H, (1 : ℝ) / n ≤ Real.log ((M : ℝ) / (x : ℝ))
  have hx : 0 < x := by dsimp [x]; omega
  have hfirst : x + 1 = f 0 := by dsimp [x]; omega
  have hspan : f 0 < M := hmono 0 (k - 1) (by omega) (by omega)
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hMR : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hinj : Set.InjOn f (↑(range k) : Set ℕ) := by
    intro i hi j hj hij
    rcases lt_trichotomy i j with h | h | h
    · exact ((hmono i j h (mem_range.mp hj)).ne hij).elim
    · exact h
    · exact ((hmono j i h (mem_range.mp hi)).ne hij.symm).elim
  have hsumD : ∑ n ∈ D, (1 : ℝ) / n = 1 := by
    rw [show D = (range k).image f from rfl, sum_image hinj]
    simpa only [Rat.cast_sum, Rat.cast_div, Rat.cast_one, Rat.cast_natCast] using
      congrArg (fun r : ℚ => (r : ℝ)) hsum
  have hdisj : Disjoint D H := by
    apply disjoint_left.mpr
    intro n hn
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hn
    exact hmiss i (mem_range.mp hi)
  have hDsub : D ⊆ Icc (x + 1) M := by
    intro n hn
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hn
    have hik := mem_range.mp hi
    rw [hfirst]
    refine mem_Icc.mpr ⟨?_, ?_⟩
    · rcases Nat.eq_zero_or_pos i with h | h
      · rw [h]
      · exact (hmono 0 i h hik).le
    · rcases eq_or_lt_of_le (show i ≤ k - 1 by omega) with h | h
      · rw [h]
      · exact (hmono i (k - 1) h (by omega)).le
  have hHsub : H ⊆ Icc (x + 1) M := by
    intro n hn
    rw [hfirst]
    exact mem_Icc.mpr (hH n hn)
  have hsucc : (Ico x M).image (fun n => n + 1) = Icc (x + 1) M := by
    ext n
    simp only [mem_image, mem_Ico, mem_Icc]
    refine ⟨?_, ?_⟩
    · rintro ⟨j, ⟨hl, hh⟩, rfl⟩
      omega
    · rintro ⟨hl, hh⟩
      exact ⟨n - 1, ⟨by omega, by omega⟩, by omega⟩
  have hanti : AntitoneOn (fun t : ℝ => 1 / t) (Set.Icc (x : ℝ) (M : ℝ)) := by
    intro y hy z _ hyz
    exact one_div_le_one_div_of_le (hxR.trans_le hy.1) hyz
  calc
    _ = ∑ n ∈ D ∪ H, (1 : ℝ) / n := by rw [sum_union hdisj, hsumD]
    _ ≤ ∑ n ∈ Icc (x + 1) M, (1 : ℝ) / n :=
      sum_le_sum_of_subset_of_nonneg (union_subset hDsub hHsub) (fun _ _ _ => by positivity)
    _ = ∑ n ∈ Ico x M, (1 : ℝ) / ((n + 1 : ℕ) : ℝ) := by
      rw [← hsucc, sum_image (fun _ _ _ _ h => Nat.add_right_cancel h)]
    _ ≤ ∫ t in (x : ℝ)..(M : ℝ), 1 / t := AntitoneOn.sum_le_integral_Ico (by omega) hanti
    _ = _ := integral_one_div_of_pos hxR hMR

