-- Prove2me | solution 1 for FedergruenTzur.MinPred.identity_1a
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T02:14:12.456295+00:00
-- url     : https://prove2.me/submissions/689b612c-6e86-43a0-8608-dad3556de869

import Mathlib
import Definitions.Def_FedergruenTzur_MinPred_Model

set_option autoImplicit false

open FedergruenTzur.MinPred FedergruenTzur.MinPred.LotSizing in
theorem FT613_H_diff (P : LotSizing) (i k : ℕ) (hi : 1 ≤ i) (hik : i ≤ k) :
    P.H (k - 1) - P.H (i - 1) = ∑ r ∈ Finset.Ico i k, P.h r := by
  have hH : ∀ n : ℕ, 1 ≤ n → P.H (n - 1) = ∑ r ∈ Finset.Ico 1 n, P.h r := by
    intro n hn
    unfold LotSizing.H
    rw [show Finset.Icc 1 (n - 1) = Finset.Ico 1 n from by
      ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega]
  rw [hH k (by omega), hH i hi, ← Finset.sum_Ico_consecutive _ hi hik]
  ring

open FedergruenTzur.MinPred.LotSizing in
open FedergruenTzur.MinPred in
theorem solution (P : FedergruenTzur.MinPred.LotSizing) (i k j : ℕ) (hi : 1 ≤ i) (hik : i < k) (hkj : k < j) :
    P.S i j = P.S i k + P.S k j + (P.D j - P.D k) * (P.H (k - 1) - P.H (i - 1)) := by
  rw [FT613_H_diff P i k hi hik.le]
  unfold LotSizing.S
  rw [← Finset.sum_Ico_consecutive _ hik.le hkj.le, Finset.mul_sum, add_right_comm,
    ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  ring
