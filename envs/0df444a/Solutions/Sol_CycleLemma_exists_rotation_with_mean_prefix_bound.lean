-- Prove2me | solution 1 for CycleLemma.exists_rotation_with_mean_prefix_bound
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T06:46:36.064418+00:00
-- url     : https://prove2.me/submissions/da0e28b7-5a8f-4515-ba8f-43f435ede5f6

import Mathlib

private theorem exists_rotation_with_nonpositive_prefix_sums (l : List ℤ) (h : l.sum ≤ 0) :
    ∃ r ≤ l.length, ∀ j ≤ l.length, ((l.rotate r).take j).sum ≤ 0 := by
  let P (i : ℕ) := (l.take i).sum
  obtain ⟨r,hr,hm⟩ := Finset.exists_max_image (Finset.range (l.length+1)) P
    ⟨0,Finset.mem_range.mpr (Nat.succ_pos _)⟩
  have hrl : r ≤ l.length := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
  have hmax (i : ℕ) (hi : i ≤ l.length) : P i ≤ P r := hm i (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  refine ⟨r,hrl,?_⟩
  intro j hj
  rw [List.rotate_eq_drop_append_take hrl]
  by_cases hjr : j ≤ l.length-r
  · rw [List.take_append_of_le_length (by simpa using hjr)]
    have he : P (r+j) = P r + ((l.drop r).take j).sum := by
      simp only [P, List.take_add, List.sum_append]
    have hle := hmax (r+j) (by omega)
    omega
  · rw [List.take_append, List.length_drop]
    rw [List.take_of_length_le (by simpa using (show l.length-r ≤ j by omega))]
    rw [List.take_take, Nat.min_eq_left (by omega : j-(l.length-r) ≤ r), List.sum_append]
    have hdecomp : P r + (l.drop r).sum = l.sum := by
      simp only [P, ← List.sum_append, List.take_append_drop]
    have hle := hmax (j-(l.length-r)) (by omega)
    change (l.drop r).sum + P (j-(l.length-r)) ≤ 0
    omega



private theorem weighted_sum (w : List ℕ) (d t : ℤ) :
    (w.map (fun a : ℕ => d*(a : ℤ)-t)).sum = d*(w.sum : ℤ)-t*(w.length : ℤ) := by
  induction w with
  | nil => simp
  | cons a w ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one,ih]
    ring

theorem solution (w : List ℕ) :
    ∃ r ≤ w.length, ∀ j ≤ w.length,
      w.length * ((w.rotate r).take j).sum ≤ j * w.sum := by
  let f (a : ℕ) : ℤ := (w.length : ℤ)*(a : ℤ)-(w.sum : ℤ)
  let l := w.map f
  have hzero : l.sum = 0 := by
    simp only [l,f,weighted_sum]
    ring
  obtain ⟨r,hr,hle⟩ := exists_rotation_with_nonpositive_prefix_sums l (by omega)
  have hlen : l.length = w.length := List.length_map f
  rw [hlen] at hr hle
  refine ⟨r,hr,?_⟩
  intro j hj
  have hh := hle j hj
  change (((w.map f).rotate r).take j).sum ≤ 0 at hh
  rw [← List.map_rotate, ← List.map_take] at hh
  dsimp only [f] at hh
  rw [weighted_sum, List.length_take, List.length_rotate, Nat.min_eq_left hj] at hh
  have hq : (w.length : ℤ)*((((w.rotate r).take j).sum : ℕ) : ℤ) ≤ (j : ℤ)*(w.sum : ℤ) := by
    nlinarith only [hh]
  exact_mod_cast hq
