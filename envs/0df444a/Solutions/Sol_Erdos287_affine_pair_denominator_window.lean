-- Prove2me | solution 1 for Erdos287.affine_pair_denominator_window
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T09:05:36.996538+00:00
-- url     : https://prove2.me/submissions/344f0878-4bca-4bd0-820e-b13c2bdf5362

import Mathlib

set_option autoImplicit false

/-- Place a compatible affine pair in the denominator window using general distance bounds. -/
theorem solution (a b t M : ℕ) (Q d V dLo dHi tLo tHi cLo cHi ε : ℝ)
    (hM : 0 < M) (hab : a < b) (hdiv : (b - a) ∣ a)
    (hd : 0 < d) (hV : 0 < V)
    (hcLo : 0 ≤ cLo) (hcHi : 0 ≤ cHi) (hε : ε ≤ 1)
    (hdlo : dLo * V / M ≤ d) (hdhi : d ≤ dHi * V / M)
    (htlo : tLo * V ≤ Q * t) (hthi : Q * t ≤ tHi * V)
    (hcoeflo : cLo * Q / d ≤ ((a / (b - a) : ℕ) : ℝ) * b)
    (hcoefhi : ((a / (b - a) : ℕ) : ℝ) * b ≤ cHi * Q / d)
    (hWindowLo : (37 / 100 : ℝ) * dHi < cLo * tLo)
    (hWindowHi : cHi * tHi ≤ (1 - ε) * dLo)
    (herror : ((a / (b - a) + 1 : ℕ) : ℝ) ≤ ε * (M : ℝ)) :
    ∃ x : ℕ, 0 < x ∧ (b * t + 1) ∣ x ∧ (a * t + 1) ∣ (x + 1) ∧
      x + 1 ≤ M ∧ (M : ℝ) < Real.exp 1 * x := by
  let c := a / (b - a)
  let x := c * (b * t + 1)
  have hc : c * (b - a) = a := Nat.div_mul_cancel hdiv
  have hcb : (c + 1) * (b - a) = b := by
    rw [add_mul, one_mul, hc]
    omega
  have hsucc : x + 1 = (c + 1) * (a * t + 1) := calc
    x + 1 = c * (((c + 1) * (b - a)) * t + 1) + 1 :=
      congrArg (fun z : ℕ => c * (z * t + 1) + 1) hcb.symm
    _ = (c + 1) * ((c * (b - a)) * t + 1) := by ring
    _ = _ := by rw [hc]
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  have hdlo' := (div_le_iff₀ hm).mp hdlo
  have hdhi' := (le_div_iff₀ hm).mp hdhi
  have hcoeflo' := (div_le_iff₀ hd).mp hcoeflo
  have hcoefhi' := (le_div_iff₀ hd).mp hcoefhi
  let y := (c : ℝ) * b * t
  have hx : (x : ℝ) = y + c := by simp [x, y, mul_add, mul_assoc]
  have hmullo : (cLo * tLo) * V ≤ y * d := by
    have h₁ := mul_le_mul_of_nonneg_left htlo hcLo
    have h₂ := mul_le_mul_of_nonneg_right hcoeflo' (Nat.cast_nonneg t)
    dsimp [y, c]
    nlinarith only [h₁, h₂]
  have hmulhi : y * d ≤ (cHi * tHi) * V := by
    have h₁ := mul_le_mul_of_nonneg_left hthi hcHi
    have h₂ := mul_le_mul_of_nonneg_right hcoefhi' (Nat.cast_nonneg t)
    dsimp [y, c]
    nlinarith only [h₁, h₂]
  have hylo : (37 / 100 : ℝ) * M < y := by
    refine lt_of_mul_lt_mul_right ?_ hd.le
    have h := mul_le_mul_of_nonneg_left hdhi' (show (0 : ℝ) ≤ 2 / 5 by norm_num)
    have hm' := mul_lt_mul_of_pos_right hWindowLo hV
    nlinarith only [h, hmullo, hm']
  have hyhi : y ≤ (1 - ε) * M := by
    refine le_of_mul_le_mul_right ?_ hd
    have h := mul_le_mul_of_nonneg_left hdlo' (sub_nonneg.mpr hε)
    have hm' := mul_le_mul_of_nonneg_right hWindowHi hV.le
    nlinarith only [h, hmulhi, hm']
  have hxle : x + 1 ≤ M := by
    have h : (x : ℝ) + 1 ≤ M := by
      rw [hx]
      push_cast at herror
      change (c : ℝ) + 1 ≤ ε * (M : ℝ) at herror
      nlinarith only [hyhi, herror]
    exact_mod_cast h
  have hₑ : (100 / 37 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hc₀ : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  have hxpos : (0 : ℝ) < x := by rw [hx]; linarith only [hc₀, hm, hylo]
  have hMlo : (M : ℝ) < (100 / 37 : ℝ) * x := by
    rw [hx]
    linarith only [hc₀, hylo]
  refine ⟨x, by exact_mod_cast hxpos, dvd_mul_left _ _, ?_, hxle, hMlo.trans (mul_lt_mul_of_pos_right hₑ hxpos)⟩
  rw [hsucc]
  exact dvd_mul_left _ _

