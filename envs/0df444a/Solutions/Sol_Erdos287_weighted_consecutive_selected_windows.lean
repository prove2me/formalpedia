-- Prove2me | solution 1 for Erdos287.weighted_consecutive_selected_windows
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T15:00:01.256548+00:00
-- url     : https://prove2.me/submissions/900db439-ccea-49a4-a2d0-50ef7067d126

import Mathlib

open Finset

set_option autoImplicit false

/-- Weighting a window by the reciprocal of its last position charges the
window no more than the reciprocal of any omitted denominator inside it. -/
theorem solution (D : Finset ℕ) (m M w : ℕ) (hm : 0 < m) (hw : 0 < w)
    (hD : D ⊆ Finset.Icc m M) (hsum : ∑ n ∈ D, (1 : ℝ) / n = 1) :
    let ends := Finset.Icc (m + w - 1) M
    let full := ends.filter (fun n => ∀ i ∈ Finset.range w, n - i ∈ D)
    (∑ n ∈ ends, (1 : ℝ) / n) - w * ((∑ n ∈ Finset.Icc m M, (1 : ℝ) / n) - 1) ≤
      ∑ n ∈ full, (1 : ℝ) / n := by
  classical
  let I := Icc m M
  let R := Icc (m + w - 1) M
  let G := R.filter (fun n => ∀ i ∈ range w, n - i ∈ D)
  let H := I \ D
  let F (n : ℕ) := (1 : ℝ) / n
  let U (i n : ℕ) := if n - i ∈ H then F (n - i) else 0
  change (∑ n ∈ R, F n) - (w : ℝ) * ((∑ n ∈ I, F n) - 1) ≤ ∑ n ∈ G, F n
  have hpoint (n : ℕ) (hn : n ∈ R \ G) : F n ≤ ∑ i ∈ range w, U i n := by
    obtain ⟨hnR, hnG⟩ := mem_sdiff.mp hn
    obtain ⟨hnlo, hnhi⟩ := mem_Icc.mp hnR
    have hnot : ¬∀ i ∈ range w, n - i ∈ D := fun h => hnG (mem_filter.mpr ⟨hnR, h⟩)
    push Not at hnot
    obtain ⟨i, hi, hmiss⟩ := hnot
    have hiw := mem_range.mp hi
    have hhole : n - i ∈ H := mem_sdiff.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, hmiss⟩
    have hpos : (0 : ℝ) < ((n - i : ℕ) : ℝ) := by exact_mod_cast (show 0 < n - i by omega)
    have hle : F n ≤ F (n - i) := one_div_le_one_div_of_le hpos (by exact_mod_cast Nat.sub_le n i)
    refine hle.trans ?_
    have heq : U i n = F (n - i) := if_pos hhole
    rw [← heq]
    exact single_le_sum (f := fun j => U j n) (fun j _ => by dsimp [U, F]; split <;> positivity) hi
  have hshift (i : ℕ) (hi : i ∈ range w) :
      (∑ n ∈ R \ G, U i n) ≤ ∑ y ∈ H, F y := by
    let T := (R \ G).filter (fun n => n - i ∈ H)
    have ht (n : ℕ) (hn : n ∈ T) : i ≤ n := by
      have hnlo := (mem_Icc.mp (mem_sdiff.mp (mem_filter.mp hn).1).1).1
      have hiw := mem_range.mp hi
      omega
    have hinj : Set.InjOn (fun n => n - i) (↑T : Set ℕ) := by
      intro a ha b hb he
      have htA := ht a ha
      have htB := ht b hb
      change a - i = b - i at he
      omega
    have himage : T.image (fun n => n - i) ⊆ H := by
      intro y hy
      obtain ⟨n, hn, rfl⟩ := mem_image.mp hy
      exact (mem_filter.mp hn).2
    calc
      _ = ∑ n ∈ T, F (n - i) := by simp only [U, T, sum_filter]
      _ = ∑ y ∈ T.image (fun n => n - i), F y := (sum_image hinj).symm
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg himage (fun y _ _ => by dsimp [F]; positivity)
  have hbad : (∑ n ∈ R \ G, F n) ≤ (w : ℝ) * ∑ n ∈ H, F n := calc
    _ ≤ ∑ n ∈ R \ G, ∑ i ∈ range w, U i n := sum_le_sum hpoint
    _ = ∑ i ∈ range w, ∑ n ∈ R \ G, U i n := sum_comm
    _ ≤ ∑ _i ∈ range w, ∑ n ∈ H, F n := sum_le_sum hshift
    _ = _ := by simp [nsmul_eq_mul]
  have hHS : (∑ n ∈ H, F n) = (∑ n ∈ I, F n) - 1 := by
    have hs := sum_sdiff (f := F) hD
    change (∑ n ∈ H, F n) + (∑ n ∈ D, F n) = ∑ n ∈ I, F n at hs
    change (∑ n ∈ D, F n) = 1 at hsum
    linarith
  have hRS : (∑ n ∈ R \ G, F n) + (∑ n ∈ G, F n) = ∑ n ∈ R, F n := sum_sdiff (filter_subset _ _)
  rw [hHS] at hbad
  linarith

