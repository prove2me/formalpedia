-- Prove2me | solution 1 for Erdos77.binomial_entropy_integer_form
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-27T19:51:41.088911+00:00
-- url     : https://prove2.me/submissions/a2a9e66a-2ca4-4739-88d0-e4a7afc65d7e

import Mathlib
open Finset

namespace Erdos77

private theorem choose_id (n j : Nat) (h : j < n) :
    (j + 1) * n.choose (j + 1) = (n - j) * n.choose j := by
  have hn : n - 1 + 1 = n := by omega
  have h1 := Nat.add_one_mul_choose_eq (n - 1) j
  have h2 := Nat.choose_mul_succ_eq (n - 1) j
  rw [hn] at h1 h2
  calc (j + 1) * n.choose (j + 1) = n.choose (j + 1) * (j + 1) := Nat.mul_comm _ _
    _ = n * (n - 1).choose j := h1.symm
    _ = (n - 1).choose j * n := Nat.mul_comm _ _
    _ = n.choose j * (n - j) := h2
    _ = (n - j) * n.choose j := Nat.mul_comm _ _

private theorem peel (a n k : Nat) (h : n = k + 1) : a ^ n = a ^ k * a := by
  rw [h, pow_succ]
/-- The summand at `j+1` dominates the one at `j` whenever `j < r < n`. -/
private theorem up_step (n r j : Nat) (hrn : r < n) (hjr : j < r) :
    n.choose j * r ^ j * (n - r) ^ (n - j)
      <= n.choose (j + 1) * r ^ (j + 1) * (n - r) ^ (n - j - 1) := by
  have h1a : j + 1 <= r := by omega
  have hmul : n.choose j * (n - r) <= n.choose (j + 1) * r :=
    calc n.choose j * (n - r) ≤ n.choose j * (n - j) := Nat.mul_le_mul_left _ (by omega)
      _ = (j + 1) * n.choose (j + 1) := by rw [choose_id n j (by omega)]; ring
      _ ≤ n.choose (j + 1) * r := by
        calc (j + 1) * n.choose (j + 1) = n.choose (j + 1) * (j + 1) := Nat.mul_comm _ _
          _ ≤ n.choose (j + 1) * r := Nat.mul_le_mul_left _ h1a
  calc n.choose j * r ^ j * (n - r) ^ (n - j)
      = (n.choose j * (n - r)) * (r ^ j * (n - r) ^ (n - j - 1)) := by
        rw [peel (n - r) (n - j) (n - j - 1) (by omega)]; ring
    _ <= (n.choose (j + 1) * r) * (r ^ j * (n - r) ^ (n - j - 1)) :=
        Nat.mul_le_mul_right _ hmul
    _ = n.choose (j + 1) * r ^ (j + 1) * (n - r) ^ (n - j - 1) := by rw [pow_succ]; ring

/-- The summand at `j-1` dominates the one at `j` whenever `r < j <= n`. -/
private theorem down_step (n r j : Nat) (hrn : r < n) (hjr : r < j) (hjn : j <= n) :
    n.choose j * r ^ j * (n - r) ^ (n - j)
      <= n.choose (j - 1) * r ^ (j - 1) * (n - r) ^ (n - j + 1) := by
  have hje : j - 1 + 1 = j := by omega
  have hc := choose_id n (j - 1) (by omega)
  rw [hje] at hc
  have hmul : n.choose j * r <= n.choose (j - 1) * (n - r) :=
    calc n.choose j * r ≤ n.choose j * j := Nat.mul_le_mul_left _ (by omega)
      _ = j * n.choose j := Nat.mul_comm _ _
      _ = (n - (j - 1)) * n.choose (j - 1) := hc
      _ = n.choose (j - 1) * (n - j + 1) := by rw [show n - (j - 1) = n - j + 1 from by omega, Nat.mul_comm]
      _ ≤ n.choose (j - 1) * (n - r) := Nat.mul_le_mul_left (n.choose (j - 1)) (by omega)
  calc n.choose j * r ^ j * (n - r) ^ (n - j)
      = (n.choose j * r) * (r ^ (j - 1) * (n - r) ^ (n - j)) := by
        rw [peel r j (j - 1) hje.symm]; ring
    _ <= (n.choose (j - 1) * (n - r)) * (r ^ (j - 1) * (n - r) ^ (n - j)) :=
        Nat.mul_le_mul_right _ hmul
    _ = n.choose (j - 1) * r ^ (j - 1) * (n - r) ^ (n - j + 1) := by
        rw [peel (n - r) (n - j + 1) (n - j) (by omega)]; ring

/-- The summand at `r - d` is bounded by the summand at `r`. -/
private theorem below (n r : Nat) (hrn : r < n) :
    forall d : Nat, d <= r -> r - d <= n ->
      n.choose (r - d) * r ^ (r - d) * (n - r) ^ (n - (r - d))
        <= n.choose r * r ^ r * (n - r) ^ (n - r) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hdk hk
    rcases Nat.eq_zero_or_pos d with hd | hd
    · rw [hd, Nat.sub_zero]
    · have h1 := up_step n r (r - d) hrn (by omega)
      have h2 := ih (d - 1) (by omega) (by omega) (by omega)
      rw [show r - d + 1 = r - (d - 1) from by omega,
        show n - (r - d) - 1 = n - (r - (d - 1)) from by omega] at h1
      exact le_trans h1 h2

/-- The summand at `r + d` is bounded by the summand at `r`. -/
private theorem above (n r : Nat) (hrn : r < n) :
    forall d : Nat, r + d <= n ->
      n.choose (r + d) * r ^ (r + d) * (n - r) ^ (n - (r + d))
        <= n.choose r * r ^ r * (n - r) ^ (n - r) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hk
    rcases Nat.eq_zero_or_pos d with hd | hd
    · rw [hd, Nat.add_zero]
    · have h1 := down_step n r (r + d) hrn (by omega) hk
      have h2 := ih (d - 1) (by omega) (by omega)
      rw [show (r + d) - 1 = r + (d - 1) from by omega,
        show n - (r + d) + 1 = n - (r + (d - 1)) from by omega] at h1
      exact le_trans h1 h2

/-- The summand at `r` dominates every other summand. -/
private theorem term_le (n r : Nat) (hrn : r < n) :
    forall j : Nat, j <= n ->
      n.choose j * r ^ j * (n - r) ^ (n - j)
        <= n.choose r * r ^ r * (n - r) ^ (n - r) := by
  intro j hj
  rcases lt_trichotomy j r with hlt | heq | hgt
  · have h := below n r hrn (r - j) (by omega) (by omega)
    rwa [show r - (r - j) = j from by omega] at h
  · rw [heq]
  · have h := above n r hrn (j - r) (by omega)
    rwa [show r + (j - r) = j from by omega] at h

end Erdos77
open Erdos77

/-- Multiplicative binomial entropy bound: the binomial theorem, plus the fact
that the summand at `j = r` is the largest of the `n+1` summands. -/
theorem solution (n r : Nat) (hr : 0 < r) (hrn : r < n) :
    (n : Real) ^ n <= ((n + 1 : Nat) : Real) * (Nat.choose n r : Real) *
      (r : Real) ^ r * (Nat.cast (n - r) : Real) ^ (n - r) := by
  have hexp : n ^ n = ∑ j ∈ range (n + 1), n.choose j * r ^ j * (n - r) ^ (n - j) := by
    have h := add_pow r (n - r) n
    rw [Nat.add_sub_of_le hrn.le] at h
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  have hbound : ∀ j ∈ range (n + 1), n.choose j * r ^ j * (n - r) ^ (n - j)
      <= n.choose r * r ^ r * (n - r) ^ (n - r) :=
    fun j hj => term_le n r hrn j (by simpa using hj)
  have hcard : (∑ j ∈ range (n + 1), n.choose j * r ^ j * (n - r) ^ (n - j))
      <= (n + 1) * (n.choose r * r ^ r * (n - r) ^ (n - r)) := by
    have h := Finset.sum_le_card_nsmul (range (n + 1))
      (fun j => n.choose j * r ^ j * (n - r) ^ (n - j))
      (n.choose r * r ^ r * (n - r) ^ (n - r)) hbound
    simpa [Nat.nsmul_eq_mul, Finset.card_range] using h
  have hnat := Nat.le_trans hexp.le hcard
  have hcast : ((n ^ n : Nat) : Real)
      <= (((n + 1) * (n.choose r * r ^ r * (n - r) ^ (n - r) : Nat) : Nat) : Real) :=
    Nat.cast_le.mpr hnat
  have hpow : ((n ^ n : Nat) : Real) = (n : Real) ^ n := by rw [← Nat.cast_pow]
  have hrhs : (((n + 1) * (n.choose r * r ^ r * (n - r) ^ (n - r) : Nat) : Nat) : Real)
      = ((n + 1 : Nat) : Real) * (Nat.choose n r : Real) *
        (r : Real) ^ r * (Nat.cast (n - r) : Real) ^ (n - r) := by
    push_cast; ring
  rwa [hpow, hrhs] at hcast
