-- Prove2me | solution 1 for Erdos287.sparse_reciprocal_corrections_on_endpoint_windows
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T16:30:16.292601+00:00
-- url     : https://prove2.me/submissions/1e09bde0-a8d2-45b6-80fa-36ee8b0741d2

import Mathlib

open Finset

set_option autoImplicit false

private theorem one_div_le_log_step (n : ℕ) (hn : 0 < n) :
    (1 : ℝ) / n ≤ Real.log (2 * (n : ℝ) + 1) - Real.log (2 * (n : ℝ) - 1) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hden : 0 < 2 * (n : ℝ) - 1 := by linarith
  let x : ℝ := 2 / (2 * (n : ℝ) - 1)
  have hx : 0 < x := div_pos (by norm_num) hden
  have hbound := Real.le_log_one_add_of_nonneg hx.le
  have hr : 2 * x / (x + 2) = (1 : ℝ) / n := by
    apply (div_eq_iff (by linarith : x + 2 ≠ 0)).2
    dsimp only [x]
    field_simp
    ring
  have hratio : 1 + x = (2 * (n : ℝ) + 1) / (2 * (n : ℝ) - 1) := by
    apply (eq_div_iff hden.ne').2
    dsimp only [x]
    field_simp
    ring
  rw [hr, hratio, Real.log_div (by positivity) hden.ne'] at hbound
  exact hbound

private theorem harmonic_midpoint_le (L U : ℕ) (hL : 0 < L) (hLU : L ≤ U) :
    (∑ n ∈ Icc L U, (1 : ℝ) / n) ≤
      Real.log ((2 * (U : ℝ) + 1) / (2 * (L : ℝ) - 1)) := by
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have htel : (∑ n ∈ Icc L U,
      (Real.log (2 * (n : ℝ) + 1) - Real.log (2 * (n : ℝ) - 1))) =
      Real.log (2 * (U : ℝ) + 1) - Real.log (2 * (L : ℝ) - 1) := by
    induction U, hLU using Nat.le_induction with
    | base => simp
    | succ U hLU ih =>
      rw [sum_Icc_succ_top (Nat.le_succ_of_le hLU), ih, Nat.cast_succ]
      have he : 2 * ((U : ℝ) + 1) - 1 = 2 * (U : ℝ) + 1 := by ring
      rw [he]
      ring
  have hsum := sum_le_sum (s := Icc L U) fun n hn =>
    one_div_le_log_step n (hL.trans_le (mem_Icc.mp hn).1)
  rw [htel] at hsum
  rw [Real.log_div (by positivity) (by linarith : 2 * (L : ℝ) - 1 ≠ 0)]
  exact hsum

/-- Correct a harmonic mass bound at a sparse set of positions, allowing
mandatory selections and certified omissions. The rest of the interval needs
only its two endpoints. -/
theorem solution (L U : ℕ) (D S H R : Finset ℕ) (c : ℕ → ℝ)
    (hL : 0 < L) (hLU : L ≤ U) (hD : D ⊆ Icc L U) (hS : S ⊆ Icc L U)
    (hH : H ⊆ S) (hdisj : Disjoint D H) (hR : R ⊆ D)
    (hsparse : ∀ n ∈ Icc L U, n ∉ S → c n = 0) :
    (∑ n ∈ D, ((1 : ℝ) / n + c n)) ≤
      Real.log ((2 * (U : ℝ) + 1) / (2 * (L : ℝ) - 1)) +
        ∑ n ∈ S, if n ∈ H then -((1 : ℝ) / n) else
          if n ∈ R then c n else max (-((1 : ℝ) / n)) (c n) := by
  let correction (n : ℕ) := if n ∈ H then -((1 : ℝ) / n) else
    if n ∈ R then c n else max (-((1 : ℝ) / n)) (c n)
  have hsel (n : ℕ) (hn : n ∈ D) : c n ≤ correction n := by
    have hno : n ∉ H := fun hh => disjoint_left.mp hdisj hn hh
    by_cases hr : n ∈ R
    · simp [correction, hno, hr]
    · simp [correction, hno, hr]
  have hother (n : ℕ) (hn : n ∉ D) : 0 ≤ (1 : ℝ) / n + correction n := by
    have hnR : n ∉ R := fun h => hn (hR h)
    by_cases hh : n ∈ H
    · simp [correction, hh]
    · simpa [correction, hh, hnR] using
        add_le_add (le_refl ((1 : ℝ) / n)) (le_max_left (-((1 : ℝ) / n)) (c n))
  have hzero (n : ℕ) (hn : n ∈ Icc L U) (hs : n ∉ S) : correction n = 0 := by
    have hno : n ∉ H := fun h => hs (hH h)
    simp [correction, hno, hsparse n hn hs]
  have hterm (n : ℕ) (hn : n ∈ D) : (1 : ℝ) / n + c n ≤ 1 / n + correction n :=
    add_le_add (le_refl _) (hsel n hn)
  have hsums : (∑ n ∈ Icc L U, correction n) = ∑ n ∈ S, correction n :=
    (sum_subset hS (fun n hn hs => hzero n hn hs)).symm
  calc
    _ ≤ ∑ n ∈ D, ((1 : ℝ) / n + correction n) := sum_le_sum hterm
    _ ≤ ∑ n ∈ Icc L U, ((1 : ℝ) / n + correction n) :=
      sum_le_sum_of_subset_of_nonneg hD (fun n _ hn => hother n hn)
    _ = (∑ n ∈ Icc L U, (1 : ℝ) / n) + ∑ n ∈ S, correction n := by
      rw [sum_add_distrib, hsums]
    _ ≤ _ := add_le_add (harmonic_midpoint_le L U hL hLU) (le_refl _)

