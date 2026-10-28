-- Prove2me | solution 1 for EssCheck.Accuracy.regime_condition
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:26:24.337772+00:00
-- url     : https://prove2.me/submissions/d7d8d331-2965-48bd-af03-d23f35198adc

import Mathlib
import Definitions.Def_EssCheck_Accuracy_Model

open EssCheck.Accuracy in
theorem solution {n : ℕ} (M : Model n) (hS : M.Standing)
    (β xh : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hx0 : 0 < xh) (hx1 : xh < 1) (i : Fin n) :
    (IsHybrid M β xh i ↔
      xh * M.pH i * M.l i ≤ (1 - β) * (1 - xh) * M.p0 i *
        (M.αbar * M.v i - M.l i)) ∧
    (0 < M.p0 i →
      (IsHybrid M β xh i ↔
        M.pH i * M.l i / (M.p0 i * (M.αbar * M.v i - M.l i)) ≤
          (1 - β) * (1 - xh) / xh)) := by
  obtain ⟨hH, _, h0, _, _, hl, hlv, _⟩ := hS
  have hpH := hH.1 i
  have hp0 := h0.1 i
  have hli := hl i
  have hlvi := hlv i
  have h1 : IsHybrid M β xh i ↔
      xh * M.pH i * M.l i ≤ (1 - β) * (1 - xh) * M.p0 i *
        (M.αbar * M.v i - M.l i) := by
    unfold IsHybrid IsHybridAt lamC
    have ha : 0 ≤ xh * M.pH i := mul_nonneg hx0.le hpH
    have hb : 0 ≤ (1 - β) * (1 - xh) * M.p0 i :=
      mul_nonneg (mul_nonneg (by linarith) (by linarith)) hp0
    set a := xh * M.pH i with hadef
    set b := (1 - β) * (1 - xh) * M.p0 i with hbdef
    by_cases hD : a + b = 0
    · have ha0 : a = 0 := by linarith
      have hb0 : b = 0 := by linarith
      rw [hD, div_zero, ha0, hb0]
      constructor
      · intro _; simp
      · intro _; linarith
    · have hDp : 0 < a + b := lt_of_le_of_ne (by linarith) (Ne.symm hD)
      have e : (1 - a / (a + b)) * M.αbar * M.v i = b * (M.αbar * M.v i) / (a + b) := by
        field_simp; ring
      rw [e, le_div_iff₀ hDp]
      constructor
      · intro h; nlinarith
      · intro h; nlinarith
  refine ⟨h1, fun hp0' => ?_⟩
  rw [h1, div_le_div_iff₀ (mul_pos hp0' (by linarith)) hx0]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith
