-- Prove2me | solution 1 for FedergruenTzur.MinPred.lemma2d_constant
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T02:26:11.972928+00:00
-- url     : https://prove2.me/submissions/7777f9bd-1e36-4df8-ab36-0fcbe2e6d786

import Mathlib
import Definitions.Def_FedergruenTzur_MinPred_Breakpoint

set_option autoImplicit false

open FedergruenTzur.MinPred in
theorem FT2d48f621_H_split (P : LotSizing) (k l : ℕ) (hk : 1 ≤ k) (hkl : k ≤ l) :
    P.H (l - 1) = P.H (k - 1) + ∑ r ∈ Finset.Ico k l, P.h r := by
  have e : ∀ i : ℕ, 1 ≤ i → P.H (i - 1) = ∑ r ∈ Finset.Ico 1 i, P.h r := by
    intro i hi
    have hs : Finset.Icc 1 (i - 1) = Finset.Ico 1 i := by
      ext r
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    unfold LotSizing.H
    rw [hs]
  rw [e l (by omega), e k hk, Finset.sum_Ico_consecutive _ hk hkl]

open FedergruenTzur.MinPred FedergruenTzur.MinPred.LotSizing in
theorem solution (P : LotSizing) (k l : ℕ) (hk : 1 ≤ k) (hkl : k < l)
    (hc : P.cij k l = P.c l) :
    (∀ x : ℝ, P.A k l + (P.cij k l - P.c l) * x = P.A k l) ∧
    (P.A k l ≠ 0 →
      ∀ x : ℝ, (0 ≤ P.A k l + (P.cij k l - P.c l) * x ↔ P.G k l ≤ (x : EReal))) := by
  have h0 : P.cij k l - P.c l = 0 := by rw [hc]; ring
  refine ⟨fun x => by rw [h0]; ring, ?_⟩
  intro hA x
  rw [h0, zero_mul, add_zero]
  have hsplit := FT2d48f621_H_split P k l hk hkl.le
  have hC : P.Ctil l = P.Ctil k := by
    unfold LotSizing.Ctil
    unfold LotSizing.cij at hc
    rw [hsplit]
    linarith
  have hG : P.G k l = if P.A k l ≤ 0 then ⊤ else ⊥ := by
    unfold LotSizing.G LotSizing.Gord
    rw [if_pos hkl.le, if_neg (by simp [hC])]
  rw [hG]
  rcases lt_or_gt_of_ne hA with h | h
  · rw [if_pos h.le]
    constructor
    · intro h'; exact absurd h' (not_le.mpr h)
    · intro h'; exact absurd h' (by simp)
  · rw [if_neg (not_le.mpr h)]
    exact ⟨fun _ => bot_le, fun _ => h.le⟩
