-- Prove2me | solution 1 for BB6Kit.lemma317
-- status  : ACCEPTED   (prove)
-- author  : @alon yuval
-- created : 2026-11-24T08:18:02.916428+00:00
-- url     : https://prove2.me/submissions/e55d0e2d-a26a-4211-9245-3478b2b9b903

import Mathlib

open Finset

theorem solution (b1 b2 b3 R S T : ℕ) (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3)
    (hgcd : Nat.gcd (Nat.gcd b1 b2) b3 = 1) (h : ¬ (b1 ≤ R ∧ b2 ≤ S ∧ b3 ≤ T)) :
    ((Finset.range (R + 1) ×ˢ Finset.range (S + 1) ×ˢ Finset.range (T + 1)).image
      (fun x => ((x.1 : ℝ) + x.2.2 * ((b1 : ℝ) / b3), (x.2.1 : ℝ) + x.2.2 * ((b2 : ℝ) / b3)))).card =
      (R + 1) * (S + 1) * (T + 1) := by
  rw [card_image_of_injOn, card_product, card_product, card_range, card_range, card_range, mul_assoc]
  intro x hx y hy hxy
  simp only [coe_product, Set.mem_prod, coe_range, Set.mem_Iio] at hx hy
  simp only [Prod.mk.injEq] at hxy
  obtain ⟨h1, h2⟩ := hxy
  have hb3ne : (b3 : ℝ) ≠ 0 := by exact_mod_cast hb3.ne'
  have hinv : (b3 : ℝ) * (b3 : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hb3ne
  rw [div_eq_mul_inv] at h1 h2
  have e1r : ((x.1 : ℝ) - y.1) * b3 = -(((x.2.2 : ℝ) - y.2.2) * b1) := by
    linear_combination (b3 : ℝ) * h1 - ((x.2.2 : ℝ) - y.2.2) * b1 * hinv
  have e2r : ((x.2.1 : ℝ) - y.2.1) * b3 = -(((x.2.2 : ℝ) - y.2.2) * b2) := by
    linear_combination (b3 : ℝ) * h2 - ((x.2.2 : ℝ) - y.2.2) * b2 * hinv
  have e1 : ((x.1 : ℤ) - y.1) * b3 = -(((x.2.2 : ℤ) - y.2.2) * b1) := by exact_mod_cast e1r
  have e2 : ((x.2.1 : ℤ) - y.2.1) * b3 = -(((x.2.2 : ℤ) - y.2.2) * b2) := by exact_mod_cast e2r
  by_cases hd : (x.2.2 : ℤ) - y.2.2 = 0
  · have hb3z : (b3 : ℤ) ≠ 0 := by exact_mod_cast hb3.ne'
    rw [hd, zero_mul, neg_zero] at e1 e2
    have r1 := (mul_eq_zero.mp e1).resolve_right hb3z
    have r2 := (mul_eq_zero.mp e2).resolve_right hb3z
    exact Prod.ext (by omega) (Prod.ext (by omega) (by omega))
  · exfalso
    apply h
    set d : ℤ := (x.2.2 : ℤ) - y.2.2 with hdd
    -- b3 divides d (Bezout)
    have hdv1 : (b3 : ℤ) ∣ d * b1 := ⟨-((x.1 : ℤ) - y.1), by linarith [e1]⟩
    have hdv2 : (b3 : ℤ) ∣ d * b2 := ⟨-((x.2.1 : ℤ) - y.2.1), by linarith [e2]⟩
    have hdv3 : (b3 : ℤ) ∣ d * b3 := dvd_mul_left _ _
    have hbez1 := Nat.gcd_eq_gcd_ab b1 b2
    have hbez2 := Nat.gcd_eq_gcd_ab (Nat.gcd b1 b2) b3
    rw [hgcd, Nat.cast_one] at hbez2
    have hdv : (b3 : ℤ) ∣ d := by
      have e : d = (d * b1) * (Nat.gcdA b1 b2 * Nat.gcdA (Nat.gcd b1 b2) b3) +
          (d * b2) * (Nat.gcdB b1 b2 * Nat.gcdA (Nat.gcd b1 b2) b3) +
          (d * b3) * Nat.gcdB (Nat.gcd b1 b2) b3 := by
        linear_combination d * hbez2 + d * Nat.gcdA (Nat.gcd b1 b2) b3 * hbez1
      rw [e]
      exact dvd_add (dvd_add (dvd_mul_of_dvd_left hdv1 _) (dvd_mul_of_dvd_left hdv2 _))
        (dvd_mul_of_dvd_left hdv3 _)
    have hle3 : (b3 : ℤ) ≤ |d| := Int.le_of_dvd (abs_pos.mpr hd) ((dvd_abs _ _).mpr hdv)
    have hdT : |d| ≤ T := by
      rw [abs_le]
      constructor <;> omega
    have hab1 : |((x.1 : ℤ) - y.1)| * b3 = |d| * b1 := by
      have := congrArg abs e1
      rw [abs_mul, abs_neg, abs_mul, abs_of_pos (show (0 : ℤ) < b3 by exact_mod_cast hb3),
        abs_of_pos (show (0 : ℤ) < b1 by exact_mod_cast hb1)] at this
      exact this
    have hab2 : |((x.2.1 : ℤ) - y.2.1)| * b3 = |d| * b2 := by
      have := congrArg abs e2
      rw [abs_mul, abs_neg, abs_mul, abs_of_pos (show (0 : ℤ) < b3 by exact_mod_cast hb3),
        abs_of_pos (show (0 : ℤ) < b2 by exact_mod_cast hb2)] at this
      exact this
    have hb3p : (0 : ℤ) < b3 := by exact_mod_cast hb3
    have hb1p : (0 : ℤ) < b1 := by exact_mod_cast hb1
    have hb2p : (0 : ℤ) < b2 := by exact_mod_cast hb2
    have hge1 : (b1 : ℤ) ≤ |((x.1 : ℤ) - y.1)| := by
      have : (b1 : ℤ) * b3 ≤ |((x.1 : ℤ) - y.1)| * b3 := by
        rw [hab1]; nlinarith
      exact le_of_mul_le_mul_right this hb3p
    have hge2 : (b2 : ℤ) ≤ |((x.2.1 : ℤ) - y.2.1)| := by
      have : (b2 : ℤ) * b3 ≤ |((x.2.1 : ℤ) - y.2.1)| * b3 := by
        rw [hab2]; nlinarith
      exact le_of_mul_le_mul_right this hb3p
    have hR : |((x.1 : ℤ) - y.1)| ≤ R := by rw [abs_le]; constructor <;> omega
    have hS : |((x.2.1 : ℤ) - y.2.1)| ≤ S := by rw [abs_le]; constructor <;> omega
    refine ⟨?_, ?_, ?_⟩ <;> omega
