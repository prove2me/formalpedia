-- Prove2me | solution 1 for Erdos287.exact_weighted_gap_balance
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T16:42:05.481976+00:00
-- url     : https://prove2.me/submissions/8491aef2-3cd2-43f3-9eb0-0d45f1c1b4cf

import Mathlib

open Finset

set_option autoImplicit false

/-- For gaps of one or two, the difference between twice the selected mass
and the full interval mass consists of endpoint terms, the unit gaps, and
the second differences across the omitted midpoints. -/
theorem solution (k : ℕ) (f : ℕ → ℕ) (w : ℕ → ℝ) (hk : 2 ≤ k)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hgap : ∀ i, i + 1 < k → f (i + 1) = f i + 1 ∨ f (i + 1) = f i + 2) :
    let U := (range (k - 1)).filter (fun i => f (i + 1) = f i + 1)
    let V := (range (k - 1)).filter (fun i => f (i + 1) = f i + 2)
    2 * (∑ i ∈ range k, w (f i)) - (∑ n ∈ Icc (f 0) (f (k - 1)), w n) =
      (w (f 0) + w (f (k - 1))) / 2 +
      (∑ i ∈ U, (w (f i) + w (f (i + 1))) / 2) +
      ∑ i ∈ V, ((w (f i) + w (f (i + 1))) / 2 - w (f i + 1)) := by
  intro U V
  let mid (i : ℕ) := (w (f i) + w (f (i + 1))) / 2
  let S := ∑ i ∈ range k, w (f i)
  let A := ∑ i ∈ V, w (f i + 1)
  have hk' : k - 1 + 1 = k := by omega
  have hl : (∑ i ∈ range (k - 1), w (f i)) + w (f (k - 1)) = S := by
    simpa only [S, hk'] using (sum_range_succ (fun i => w (f i)) (k - 1)).symm
  have hr : (∑ i ∈ range (k - 1), w (f (i + 1))) + w (f 0) = S := by
    simpa only [S, hk'] using (sum_range_succ' (fun i => w (f i)) (k - 1)).symm
  have hmid : (∑ i ∈ range (k - 1), mid i) = S - (w (f 0) + w (f (k - 1))) / 2 := by
    dsimp only [mid]
    rw [← sum_div, sum_add_distrib]
    linarith only [hl, hr]
  have hsep : (∑ i ∈ range (k - 1), mid i) = (∑ i ∈ U, mid i) + ∑ i ∈ V, mid i := by
    dsimp only [U, V]
    rw [sum_filter, sum_filter, ← sum_add_distrib]
    refine sum_congr rfl fun i hi => ?_
    rcases hgap i (by have := mem_range.mp hi; omega) with he | he
    · simp [he]
    · simp [he]
  let P (t : ℕ) := ∑ n ∈ range t, w n
  have hseg : (∑ i ∈ range (k - 1), ∑ n ∈ Ico (f i) (f (i + 1)), w n) =
      ∑ n ∈ Ico (f 0) (f (k - 1)), w n := by
    calc
      _ = ∑ i ∈ range (k - 1), (P (f (i + 1)) - P (f i)) := by
        refine sum_congr rfl fun i hi => ?_
        exact sum_Ico_eq_sub w (hmono i (i + 1) (by omega)
          (by have := mem_range.mp hi; omega)).le
      _ = P (f (k - 1)) - P (f 0) := sum_range_sub (fun i => P (f i)) (k - 1)
      _ = _ := (sum_Ico_eq_sub w (hmono 0 (k - 1) (by omega) (by omega)).le).symm
  have hone (i : ℕ) (hi : i ∈ range (k - 1)) :
      (∑ n ∈ Ico (f i) (f (i + 1)), w n) =
        w (f i) + if f (i + 1) = f i + 2 then w (f i + 1) else 0 := by
    rcases hgap i (by have := mem_range.mp hi; omega) with he | he
    · simp [he, Nat.Ico_succ_singleton]
    · rw [he, show f i + 2 = (f i + 1) + 1 by omega,
        sum_Ico_succ_top (Nat.le_succ _), Nat.Ico_succ_singleton, sum_singleton]
      simp
  have hwhole : (∑ n ∈ Icc (f 0) (f (k - 1)), w n) = S + A := by
    rw [← Ico_add_one_right_eq_Icc, sum_Ico_succ_top
      (hmono 0 (k - 1) (by omega) (by omega)).le, ← hseg]
    rw [sum_congr rfl hone, sum_add_distrib, ← sum_filter]
    change ((∑ i ∈ range (k - 1), w (f i)) + A) + w (f (k - 1)) = S + A
    linarith only [hl]
  change 2 * S - (∑ n ∈ Icc (f 0) (f (k - 1)), w n) =
    (w (f 0) + w (f (k - 1))) / 2 + (∑ i ∈ U, mid i) +
      ∑ i ∈ V, (mid i - w (f i + 1))
  rw [hwhole, sum_sub_distrib]
  change 2 * S - (S + A) = (w (f 0) + w (f (k - 1))) / 2 +
    (∑ i ∈ U, mid i) + ((∑ i ∈ V, mid i) - A)
  linarith only [hmid, hsep]

