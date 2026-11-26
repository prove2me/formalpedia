-- Prove2me | solution 1 for Erdos287.normalized_affine_pair_hits_prescribed_maximum_band
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T08:05:28.827723+00:00
-- url     : https://prove2.me/submissions/5b96c842-7b9d-489f-ae02-7e138acda9d1

import Mathlib

set_option autoImplicit false

/-- Place the consecutive multiples arising from a compatible affine pair
inside the window of one prescribed maximal denominator. -/
theorem solution (a b t M : ℕ) (Q d V : ℝ)
    (hM : 0 < M) (hab : a < b) (hdiv : (b - a) ∣ a)
    (hd : 0 < d) (hV : 0 < V)
    (hdlo : (49 / 50 : ℝ) * V / M ≤ d)
    (hdhi : d ≤ (51 / 50 : ℝ) * V / M)
    (htlo : (4 / 9 : ℝ) * V ≤ Q * t)
    (hthi : Q * t ≤ (9 / 10 : ℝ) * V)
    (hcoeflo : (999 / 1000 : ℝ) * Q / d ≤ ((a / (b - a) : ℕ) : ℝ) * b)
    (hcoefhi : ((a / (b - a) : ℕ) : ℝ) * b ≤ (101 / 100 : ℝ) * Q / d)
    (herror : ((a / (b - a) + 1 : ℕ) : ℝ) ≤ (M : ℝ) / 100) :
    ∃ x : ℕ, (b * t + 1) ∣ x ∧ (a * t + 1) ∣ (x + 1) ∧
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
  have hmullo : ((999 / 1000) * (4 / 9) : ℝ) * V ≤ y * d := by
    have h₁ := mul_le_mul_of_nonneg_left htlo (show (0 : ℝ) ≤ 999 / 1000 by norm_num)
    have h₂ := mul_le_mul_of_nonneg_right hcoeflo' (Nat.cast_nonneg t)
    dsimp [y, c]
    nlinarith only [h₁, h₂]
  have hmulhi : y * d ≤ ((101 / 100) * (9 / 10) : ℝ) * V := by
    have h₁ := mul_le_mul_of_nonneg_left hthi (show (0 : ℝ) ≤ 101 / 100 by norm_num)
    have h₂ := mul_le_mul_of_nonneg_right hcoefhi' (Nat.cast_nonneg t)
    dsimp [y, c]
    nlinarith only [h₁, h₂]
  have hylo : (2 / 5 : ℝ) * M < y := by
    refine lt_of_mul_lt_mul_right ?_ hd.le
    have h := mul_le_mul_of_nonneg_left hdhi' (show (0 : ℝ) ≤ 2 / 5 by norm_num)
    nlinarith only [h, hmullo, hV]
  have hyhi : y ≤ (99 / 100 : ℝ) * M := by
    refine le_of_mul_le_mul_right ?_ hd
    have h := mul_le_mul_of_nonneg_left hdlo' (show (0 : ℝ) ≤ 99 / 100 by norm_num)
    nlinarith only [h, hmulhi, hV]
  have hxle : x + 1 ≤ M := by
    have h : (x : ℝ) + 1 ≤ M := by
      rw [hx]
      push_cast at herror
      change (c : ℝ) + 1 ≤ (M : ℝ) / 100 at herror
      linarith only [hyhi, herror]
    exact_mod_cast h
  have hₑ : (5 / 2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hc₀ : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  have hxpos : (0 : ℝ) < x := by rw [hx]; linarith only [hc₀, hm, hylo]
  have hMlo : (M : ℝ) < (5 / 2 : ℝ) * x := by
    rw [hx]
    linarith only [hc₀, hylo]
  refine ⟨x, dvd_mul_left _ _, ?_, hxle, hMlo.trans (mul_lt_mul_of_pos_right hₑ hxpos)⟩
  rw [hsucc]
  exact dvd_mul_left _ _

