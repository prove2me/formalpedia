-- Prove2me | solution 1 for FoodTrace.Adoption.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T09:59:51.508004+00:00
-- url     : https://prove2.me/submissions/38e79e9a-9de0-4747-a58b-ba0d79b14602

import Mathlib
import Definitions.Def_FoodTrace_Adoption_Model

open FoodTrace.Adoption

theorem solution (P : Params) (hP : Standing P) (hBPC : BPC P) :
    rNe P < rTe P ∧ 1 - P.ρ < (1 - P.ρe) ^ P.n := by
  obtain ⟨hn, hρe, hρ, hρ1, he, hcp, hbar⟩ := hP
  set A := 1 - P.ρe with hA
  set B := 1 - P.ρ with hB
  have hτ : ρτ P = A - B := by unfold ρτ; rw [hA, hB]; ring
  have hτpos : 0 < ρτ P := by rw [hτ]; linarith
  have hBpos : 0 < B := by linarith
  have hApos : 0 < A := by linarith
  have hA1 : A ≤ 1 := by linarith
  have hB1 : B < 1 := by linarith
  have hbar' : P.cp * ρτ P < B * P.e := by
    unfold cpBar at hbar; rw [lt_div_iff₀ hτpos] at hbar; rw [hB]; linarith
  set N : ℝ := (P.n : ℝ) with hN
  have hNpos : 0 < N := by rw [hN]; exact_mod_cast (show 0 < P.n by omega)
  set a := A ^ P.n with ha
  set b := B ^ P.n with hb
  have hapos : 0 < a := pow_pos hApos _
  have hbB : b < B := by
    rw [hb]; calc B ^ P.n < B ^ 1 := pow_lt_pow_right_of_lt_one₀ hBpos hB1 (by omega)
      _ = B := pow_one B
  have hba : b < a := pow_lt_pow_left₀ (by linarith) hBpos.le (by omega)
  have hℓ : ell P = a - b := rfl
  have hℓpos : 0 < ell P := by rw [hℓ]; linarith
  -- p^e_N ≥ e/τ > c_p/B
  have hAm : 0 < A ^ (P.n - 1) := pow_pos hApos _
  have hAm1 : A ^ (P.n - 1) ≤ 1 := pow_le_one₀ hApos.le hA1
  have hpNe : P.e / ρτ P ≤ pNe P := by
    unfold pNe
    exact div_le_div_of_nonneg_left he.le (mul_pos hτpos hAm)
      (by nlinarith)
  have hcpB : P.cp / B < P.e / ρτ P := by
    rw [div_lt_div_iff₀ hBpos hτpos]; linarith
  have hwNe : pNe P ≤ wNe P := le_max_right _ _
  have hwB : P.cp / B < wNe P := by linarith
  have hpB : P.cp / B < pNe P := by linarith
  -- r^e_T > c_p / B
  have hrTe : P.cp / B < rTe P := by
    have h1 : rTe P = (A ^ 2 * P.e - (1 + P.ρ - 2 * P.ρe) * ρτ P * P.cp) / ρτ P ^ 3 := rfl
    rw [h1, div_lt_div_iff₀ hBpos (pow_pos hτpos 3)]
    have h2 : 1 + P.ρ - 2 * P.ρe = A + ρτ P := by rw [hτ, hA, hB]; ring
    rw [h2]
    have hAe : A = B + ρτ P := by rw [hτ]; ring
    have key : B * (A ^ 2 * P.e) = (B * P.e) * (B * (A + ρτ P) + ρτ P ^ 2) := by rw [hAe]; ring
    have hpos : 0 < B * (A + ρτ P) + ρτ P ^ 2 := by positivity
    nlinarith [mul_lt_mul_of_pos_right hbar' hpos]
  -- π^o_0T(r^e_T) = π^e_0T(r^e_T)
  have hTT : pi0Te P (rTe P) = pi0To P (rTe P) := by
    unfold pi0Te pi0To wTe rTe
    have h2 : 1 + P.ρ - 2 * P.ρe = A + ρτ P := by rw [hτ, hA, hB]; ring
    rw [h2, ← hN, ← hB]
    have hne : ρτ P ≠ 0 := hτpos.ne'
    have hAe : A = B + ρτ P := by rw [hτ]; ring
    rw [← hA, hAe]
    field_simp
    ring
  have hD1 : B * rTe P - P.cp < a * (rTe P - wNe P) := by
    have h := hBPC
    unfold BPC at h
    rw [hTT] at h
    unfold pi0To pi0Ne at h
    rw [← hN, ← hB, ← hA, ← ha] at h
    have : N * (B * rTe P - P.cp) < N * (a * (rTe P - wNe P)) := by linarith
    exact lt_of_mul_lt_mul_left this hNpos.le
  -- part 2
  have hpart2 : B < a := by
    by_contra hc
    push_neg at hc
    have h3 : (a - B) * rTe P ≤ (a - B) * (P.cp / B) :=
      mul_le_mul_of_nonpos_left hrTe.le (by linarith)
    have h4 : (a - B) * (P.cp / B) = a * (P.cp / B) - P.cp := by field_simp
    have h5 : a * wNe P < a * (P.cp / B) := by linarith
    have := lt_of_mul_lt_mul_left h5 hapos.le
    linarith
  -- D(r^e_N) > 0
  have hD0 : a * (rNe P - wNe P) < B * rNe P - P.cp := by
    set F := ((1 - P.ρe) ^ (P.n + 1) * P.e
      - (2 * (1 - P.ρe) ^ P.n - (1 - P.ρ) ^ P.n) * ρτ P * P.cp) / (ρτ P * ell P ^ 2) with hF
    have hrNe : rNe P = max F (pNe P) := rfl
    rcases le_total F (pNe P) with hFp | hFp
    · rw [hrNe, max_eq_right hFp]
      have : a * (pNe P - wNe P) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hapos.le (by linarith)
      have : P.cp < B * pNe P := by rwa [div_lt_iff₀' hBpos] at hpB
      linarith
    · rw [hrNe, max_eq_left hFp]
      set G := ((1 - P.ρe) * P.e - ρτ P * P.cp) / (ρτ P * ell P) with hG
      have hGw : G ≤ wNe P := le_max_left _ _
      have hid : ell P * F = a * G - P.cp := by
        rw [hF, hG, ← hA, ← hB, ← ha, ← hb, pow_succ, ← ha]
        have hne : ρτ P ≠ 0 := hτpos.ne'
        have hne2 : ell P ≠ 0 := hℓpos.ne'
        rw [hℓ] at hne2 ⊢
        field_simp
        ring
      have hFpos : 0 < F := by
        have : 0 < pNe P := by unfold pNe; positivity
        linarith
      have h6 : a * G ≤ a * wNe P := mul_le_mul_of_nonneg_left hGw hapos.le
      have h7 : b * F < B * F := mul_lt_mul_of_pos_right hbB hFpos
      rw [hℓ] at hid
      nlinarith
  refine ⟨?_, hpart2⟩
  by_contra hc
  push_neg at hc
  have : (a - B) * (rNe P - rTe P) ≥ 0 := mul_nonneg (by linarith) (by linarith)
  nlinarith
