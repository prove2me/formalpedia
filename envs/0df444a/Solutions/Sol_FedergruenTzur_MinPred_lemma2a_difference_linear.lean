-- Prove2me | solution 1 for FedergruenTzur.MinPred.lemma2a_difference_linear
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T07:17:34.606388+00:00
-- url     : https://prove2.me/submissions/0f5a881f-41d5-4772-aa57-3ca1cc11942e

import Mathlib
import Definitions.Def_FedergruenTzur_MinPred_Breakpoint
import Definitions.Def_FedergruenTzur_MinPred_Omega

set_option autoImplicit false

open FedergruenTzur.MinPred in
theorem a5d743de_S_diff (P : LotSizing) (k m t : ℕ) (hk : k ≤ m) (hmt : m + 1 ≤ t) :
    P.S k t - P.S (m + 1) t
      = P.S k m + (∑ r ∈ Finset.Ico k (m + 1), P.h r) * (P.D t - P.D m) := by
  unfold LotSizing.S
  rw [← Finset.sum_Ico_consecutive _ (show k ≤ m + 1 by omega) hmt]
  rw [Finset.sum_Ico_succ_top hk, Finset.sum_Ico_succ_top hk, add_mul, Finset.sum_mul]
  have e : ∑ r ∈ Finset.Ico k m, P.h r * (P.D t - P.D r)
      = ∑ r ∈ Finset.Ico k m, P.h r * (P.D m - P.D r)
        + ∑ r ∈ Finset.Ico k m, P.h r * (P.D t - P.D m) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun r _ => by ring)
  rw [e]
  ring

open FedergruenTzur.MinPred in
theorem a5d743de_H_diff (P : LotSizing) (k m : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ m) :
    P.H m - P.H (k - 1) = ∑ r ∈ Finset.Ico k (m + 1), P.h r := by
  unfold LotSizing.H
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have e1 : Finset.Icc 1 m = Finset.Ico 1 (m + 1) := by ext; simp
  have e2 : Finset.Icc 1 k' = Finset.Ico 1 (k' + 1) := by ext; simp
  rw [Nat.add_sub_cancel, e1, e2,
    ← Finset.sum_Ico_consecutive _ (show 1 ≤ k' + 1 by omega) (show k' + 1 ≤ m + 1 by omega)]
  ring

open FedergruenTzur.MinPred LotSizing in
theorem solution (P : LotSizing) (k l : ℕ) (hk : 1 ≤ k) (hkl : k < l) :
    (∀ t, l ≤ t → P.Flast k t - P.Flast l t = P.A k l + (P.cij k l - P.c l) * P.D t) ∧
    (∀ j, l ≤ j → ∀ x : ℝ,
      P.potCost j k x - P.potCost j l x = P.A k l + (P.cij k l - P.c l) * x) := by
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
  have hkm : k ≤ m := by omega
  refine ⟨fun t ht => ?_, fun j hj x => ?_⟩
  · have hS := a5d743de_S_diff P k m t hkm ht
    simp only [LotSizing.Flast, LotSizing.A, LotSizing.cij, Nat.add_sub_cancel]
    linear_combination hS
  · have hS := a5d743de_S_diff P k m j hkm hj
    have hH := a5d743de_H_diff P k m hk hkm
    simp only [LotSizing.potCost, LotSizing.A, LotSizing.cij, Nat.add_sub_cancel]
    linear_combination hS + (x - P.D j) * hH
