-- Prove2me | solution 1 for FedergruenTzur.MinPred.lemma2b_increasing
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T01:00:54.480984+00:00
-- url     : https://prove2.me/submissions/d9093262-fcf3-4889-bdf1-ad3e355756e7

import Mathlib
import Definitions.Def_FedergruenTzur_MinPred_Breakpoint

namespace FedergruenTzur.MinPred

open LotSizing

theorem lemma2b_aux_Ctil (P : LotSizing) (k l : ℕ) (hk : 1 ≤ k) (hkl : k < l) :
    P.Ctil l - P.Ctil k = P.c l - P.cij k l := by
  have hIcc : ∀ m : ℕ, 1 ≤ m → Finset.Icc 1 (m - 1) = Finset.Ico 1 m := by
    intro m hm
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  have h := Finset.sum_Ico_consecutive P.h hk hkl.le
  simp only [LotSizing.Ctil, LotSizing.cij, LotSizing.H]
  rw [hIcc l (by omega), hIcc k hk, ← h]
  ring

end FedergruenTzur.MinPred

open FedergruenTzur.MinPred LotSizing in
theorem solution (P : FedergruenTzur.MinPred.LotSizing) (k l : ℕ) (hk : 1 ≤ k) (hkl : k < l)
    (hc : P.c l < P.cij k l) :
    StrictMono (fun x : ℝ => P.A k l + (P.cij k l - P.c l) * x) ∧
    ∀ x : ℝ, (0 ≤ P.A k l + (P.cij k l - P.c l) * x ↔ P.G k l ≤ (x : EReal)) := by
  have hs : 0 < P.cij k l - P.c l := by linarith
  refine ⟨?_, ?_⟩
  · intro a b hab
    simp only
    nlinarith
  · intro x
    have hC := FedergruenTzur.MinPred.lemma2b_aux_Ctil P k l hk hkl
    have hne : P.Ctil l ≠ P.Ctil k := by
      intro h; have : P.Ctil l - P.Ctil k = 0 := by rw [h, sub_self]
      linarith
    have hG : P.G k l = ((P.A k l / (P.Ctil l - P.Ctil k) : ℝ) : EReal) := by
      simp only [LotSizing.G, LotSizing.Gord, if_pos hkl.le, if_pos hne]
    rw [hG, EReal.coe_le_coe_iff, hC]
    have hneg : P.c l - P.cij k l = -(P.cij k l - P.c l) := by ring
    rw [hneg, div_neg, neg_le, ← sub_nonneg]
    constructor
    · intro h0
      have : -x ≤ P.A k l / (P.cij k l - P.c l) := by
        rw [le_div_iff₀ hs]; linarith
      linarith
    · intro h0
      have : -x ≤ P.A k l / (P.cij k l - P.c l) := by linarith
      rw [le_div_iff₀ hs] at this; linarith
