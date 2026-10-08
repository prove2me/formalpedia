-- Prove2me | solution 1 for FedergruenTzur.MinPred.lemma2c_decreasing
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T01:01:16.137029+00:00
-- url     : https://prove2.me/submissions/e62c05b4-e9c5-402c-b6c2-063ed44e9264

import Mathlib
import Definitions.Def_FedergruenTzur_MinPred_Breakpoint

set_option autoImplicit false

namespace FedergruenTzur.MinPred.LotSizing

theorem e3787c54_Ctil_sub (P : LotSizing) (k l : ℕ) (hk : 1 ≤ k) (hkl : k < l) :
    P.Ctil l - P.Ctil k = P.c l - P.cij k l := by
  have hH : P.H (l - 1) = P.H (k - 1) + ∑ r ∈ Finset.Ico k l, P.h r := by
    unfold H
    have e1 : Finset.Icc 1 (l - 1) = Finset.Ico 1 l := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    have e2 : Finset.Icc 1 (k - 1) = Finset.Ico 1 k := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    rw [e1, e2, Finset.sum_Ico_consecutive _ hk hkl.le]
  unfold Ctil cij
  rw [hH]
  ring

end FedergruenTzur.MinPred.LotSizing

open FedergruenTzur.MinPred FedergruenTzur.MinPred.LotSizing in
theorem solution (P : LotSizing) (k l : ℕ) (hk : 1 ≤ k) (hkl : k < l)
    (hc : P.cij k l < P.c l) :
    StrictAnti (fun x : ℝ => P.A k l + (P.cij k l - P.c l) * x) ∧
    ∀ x : ℝ, (0 ≤ P.A k l + (P.cij k l - P.c l) * x ↔ (x : EReal) ≤ P.G k l) := by
  have hs : 0 < P.c l - P.cij k l := sub_pos.mpr hc
  have hC := e3787c54_Ctil_sub P k l hk hkl
  refine ⟨?_, ?_⟩
  · intro a b hab
    have : (P.cij k l - P.c l) * b < (P.cij k l - P.c l) * a :=
      mul_lt_mul_of_neg_left hab (by linarith)
    simp only
    linarith
  · intro x
    have hne : P.Ctil l ≠ P.Ctil k := by intro h; rw [h, sub_self] at hC; linarith
    have hG : P.G k l = ((P.A k l / (P.Ctil l - P.Ctil k) : ℝ) : EReal) := by
      unfold G Gord
      rw [if_pos hkl.le, if_pos hne]
    rw [hG, EReal.coe_le_coe_iff, hC, le_div_iff₀ hs]
    constructor <;> intro h <;> nlinarith
