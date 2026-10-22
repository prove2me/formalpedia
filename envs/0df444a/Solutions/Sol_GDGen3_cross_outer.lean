-- Prove2me | solution 1 for GDGen3.cross_outer
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T05:55:00.092905+00:00
-- url     : https://prove2.me/submissions/ced31592-a93c-4960-be83-abb4c0b8cb75

import Mathlib
import Definitions.Def_GDGen3Base
import Theorems.Thm_GDGen3_prefix_telescope
import Theorems.Thm_GDGen3_D_telescope

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (ξ : ℕ → ℝ) (N i : ℕ) (hi : i + 1 ≤ N)
    (h0 : ξ 0 = 0) (hne : ∀ i : ℕ, i ≠ 0 → ξ i ≠ 0) :
    Finset.sum (Finset.Icc (i + 1) N)
        (fun j => (D r ξ N j + r * D r ξ N (j + 1)) * Abar ξ i
          - (D r ξ N j - D r ξ N (j + 1))
            * ((Finset.sum (Finset.range i) (fun k => Abar ξ k)) + r * Abar ξ i
                + r * (Finset.sum (Finset.range i) (fun k => Abar ξ k))))
      = (1 - r) * (Abar ξ i * D r ξ N (i + 1))
        + (1 + r) * (Abar ξ i * (Finset.sum (Finset.Icc (i + 2) N) (fun j => D r ξ N j))
            - D r ξ N (i + 1) * (Finset.sum (Finset.range i) (fun k => Abar ξ k))) := by
  have hP : Finset.sum (Finset.range i) (fun k => Abar ξ k) = ξ i * Abar ξ i :=
    prefix_telescope ξ h0 hne i
  have htel := D_telescope r ξ N i hi
  have hsplit : Finset.sum (Finset.Icc (i + 1) N)
        (fun j => (D r ξ N j + r * D r ξ N (j + 1)) * Abar ξ i
          - (D r ξ N j - D r ξ N (j + 1))
            * ((Finset.sum (Finset.range i) (fun k => Abar ξ k)) + r * Abar ξ i
                + r * (Finset.sum (Finset.range i) (fun k => Abar ξ k))))
      = Abar ξ i * Finset.sum (Finset.Icc (i + 1) N) (fun j => D r ξ N j + r * D r ξ N (j + 1))
        - ((Finset.sum (Finset.range i) (fun k => Abar ξ k)) + r * Abar ξ i
            + r * (Finset.sum (Finset.range i) (fun k => Abar ξ k)))
          * Finset.sum (Finset.Icc (i + 1) N) (fun j => D r ξ N j - D r ξ N (j + 1)) := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
    ring
  rw [hsplit, htel]
  have hre : Finset.sum (Finset.Icc (i + 1) N) (fun j => D r ξ N j + r * D r ξ N (j + 1))
      = D r ξ N (i + 1) + (1 + r) * Finset.sum (Finset.Icc (i + 2) N) (fun j => D r ξ N j) := by
    have hDN : D r ξ N (N + 1) = 0 := by
      rw [D, if_pos (Or.inr (by omega : N < N + 1))]
    rw [Finset.sum_add_distrib]
    have h2 : Finset.sum (Finset.Icc (i + 1) N) (fun j => r * D r ξ N (j + 1))
        = r * Finset.sum (Finset.Icc (i + 2) (N + 1)) (fun j => D r ξ N j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_bij (fun j _ => j + 1)
      · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
      · intro a _ b _ h; omega
      · intro b hb
        simp only [Finset.mem_Icc] at hb
        exact ⟨b - 1, by simp only [Finset.mem_Icc]; omega, by omega⟩
      · intro a _; rfl
    have hpeel : ∀ M, i + 1 ≤ M → M ≤ N →
        Finset.sum (Finset.Icc (i + 1) M) (fun j => D r ξ N j)
          = D r ξ N (i + 1) + Finset.sum (Finset.Icc (i + 2) M) (fun j => D r ξ N j) := by
      intro M h1 _
      induction M, h1 using Nat.le_induction with
      | base =>
        rw [Finset.Icc_self, Finset.sum_singleton]
        have : Finset.Icc (i + 2) (i + 1) = (∅ : Finset ℕ) := by
          apply Finset.Icc_eq_empty_of_lt
          omega
        rw [this, Finset.sum_empty, add_zero]
      | succ b hb ih =>
        rw [Finset.sum_Icc_succ_top (a := i + 1) (b := b) (by omega),
          ih (by omega), Finset.sum_Icc_succ_top (a := i + 2) (b := b) (by omega)]
        ring
    rw [h2, hpeel N (by omega) le_rfl,
      Finset.sum_Icc_succ_top (a := i + 2) (b := N) (by omega), hDN, add_zero]
    ring
  rw [hre]
  rw [hP]
  ring
