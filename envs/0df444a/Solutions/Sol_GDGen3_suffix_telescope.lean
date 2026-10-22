-- Prove2me | solution 1 for GDGen3.suffix_telescope
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T05:52:36.940104+00:00
-- url     : https://prove2.me/submissions/1259549d-441c-4e10-9f3d-bd7a7d09499a

import Mathlib
import Definitions.Def_GDGen3Base
import Theorems.Thm_GDGen3_eta_last_zero

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (N : ℕ) (hN : 1 ≤ N) (ξ : ℕ → ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hpos : ∀ i : ℕ, i ≠ 0 → 0 < ξ i) (h0 : ξ 0 = 0)
    (hquad : ∀ i : ℕ, i < N → pj r (i + 1) * ξ i * (1 + ξ i + C r N i) = X r N i)
    (hrec : eta_recur_prop r N ξ)
    (hpin : pj r N * ξ (N - 1) = X r N (N - 1)) :
    ∀ i : ℕ, i + 1 ≤ N →
      Finset.sum (Icc (i + 2) N) (fun j => D r ξ N j) = eta r N ξ i * D r ξ N (i + 1) := by
  have hlast : eta r N ξ (N - 1) = 0 :=
    eta_last_zero r N hN ξ hr hr1 hpos h0 hquad hpin
  have key : ∀ k : ℕ, ∀ i : ℕ, N - 1 - i = k → i + 1 ≤ N →
      Finset.sum (Icc (i + 2) N) (fun j => D r ξ N j) = eta r N ξ i * D r ξ N (i + 1) := by
    intro k
    induction k with
    | zero =>
      intro i hk hi
      have hiN : i = N - 1 := by omega
      subst hiN
      rw [Finset.sum_eq_zero (by intro x hx; simp only [Finset.mem_Icc] at hx; omega), hlast]
      ring
    | succ k ih =>
      intro i hk hi
      have hi2 : i + 2 ≤ N := by omega
      have hk' : N - 1 - (i + 1) = k := by omega
      have hi' : i + 1 + 1 ≤ N := by omega
      have ihk := ih (i + 1) hk' hi'
      have hsplit : Icc (i + 2) N = insert (i + 2) (Icc (i + 3) N) := by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [hsplit, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), ihk]
      have hrec' : eta r N ξ i * D r ξ N (i + 1) = D r ξ N (i + 2) * (1 + eta r N ξ (i + 1)) := by
        have h := hrec (i + 1) (by omega) hi'
        simpa only [Nat.add_sub_cancel] using h
      rw [hrec']
      ring
  intro i hi
  exact key (N - 1 - i) i rfl hi


/-! ## Section 5 layer: the flow `d`, the certificate sum, and (20) -/
