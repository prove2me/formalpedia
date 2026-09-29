-- Prove2me | solution 1 for FourExp.height_dvd_le
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-15T06:44:50.352713+00:00
-- url     : https://prove2.me/submissions/979da6ca-021a-4ad6-a8bc-0586d62a8aef

import Mathlib

open Polynomial

namespace FourExpHeight

lemma exp_sq_ge_seven : (7 : ℝ) ≤ Real.exp 1 ^ 2 := by
  have h := Real.exp_one_gt_d9
  nlinarith

/-- `d + 1 ≤ (e²/4)^d` for `d ≥ 2`. -/
lemma succ_le_pow (d : ℕ) (hd : 2 ≤ d) : (d : ℝ) + 1 ≤ (Real.exp 1 ^ 2 / 4) ^ d := by
  have h7 := exp_sq_ge_seven
  have hq : (7 : ℝ) / 4 ≤ Real.exp 1 ^ 2 / 4 := by linarith
  induction d, hd using Nat.le_induction with
  | base =>
    have : ((7 : ℝ) / 4) ^ 2 ≤ (Real.exp 1 ^ 2 / 4) ^ 2 := pow_le_pow_left₀ (by norm_num) hq 2
    push_cast
    nlinarith
  | succ n hn ih =>
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    rw [pow_succ]
    push_cast
    have hpos : 0 ≤ (Real.exp 1 ^ 2 / 4) ^ n := by positivity
    nlinarith

/-- `√(d+1) ≤ (e/2)^d` for `d ≥ 2`. -/
lemma sqrt_le_pow (d : ℕ) (hd : 2 ≤ d) : Real.sqrt ((d : ℝ) + 1) ≤ (Real.exp 1 / 2) ^ d := by
  have hsq : ((Real.exp 1 / 2) ^ d) ^ 2 = (Real.exp 1 ^ 2 / 4) ^ d := by
    rw [← pow_mul, mul_comm, pow_mul]; congr 1; ring
  have h := succ_le_pow d hd
  rw [← hsq] at h
  calc Real.sqrt ((d : ℝ) + 1) ≤ Real.sqrt (((Real.exp 1 / 2) ^ d) ^ 2) := Real.sqrt_le_sqrt h
    _ = (Real.exp 1 / 2) ^ d := Real.sqrt_sq (by positivity)

/-- The numerical factor: `C(δ, i) · √(d+1) ≤ e^d` whenever `δ ≤ d`. -/
lemma choose_sqrt_le_exp (d δ i : ℕ) (hδ : δ ≤ d) :
    ((δ.choose i : ℕ) : ℝ) * Real.sqrt ((d : ℝ) + 1) ≤ Real.exp (d : ℝ) := by
  rcases Nat.lt_or_ge d 2 with hd | hd
  · have hδ1 : δ ≤ 1 := by omega
    have hc : δ.choose i ≤ 1 :=
      (Nat.choose_le_middle i δ).trans (by interval_cases δ <;> simp)
    have hc' : ((δ.choose i : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hc
    have hs : Real.sqrt ((d : ℝ) + 1) ≤ Real.exp (d : ℝ) := by
      interval_cases d
      · simp
      · have h2 : Real.sqrt 2 ≤ 3 / 2 := by
          rw [Real.sqrt_le_left (by norm_num)]; norm_num
        have he := Real.exp_one_gt_d9
        norm_num
        linarith
    calc ((δ.choose i : ℕ) : ℝ) * Real.sqrt ((d : ℝ) + 1) ≤ 1 * Real.sqrt ((d : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right hc' (Real.sqrt_nonneg _)
      _ ≤ Real.exp (d : ℝ) := by rw [one_mul]; exact hs
  · have hc : ((δ.choose i : ℕ) : ℝ) ≤ 2 ^ d := by
      have : δ.choose i ≤ 2 ^ d := (Nat.choose_le_two_pow δ i).trans (Nat.pow_le_pow_right (by norm_num) hδ)
      exact_mod_cast this
    calc ((δ.choose i : ℕ) : ℝ) * Real.sqrt ((d : ℝ) + 1) ≤ 2 ^ d * (Real.exp 1 / 2) ^ d :=
          mul_le_mul hc (sqrt_le_pow d hd) (Real.sqrt_nonneg _) (by positivity)
      _ = Real.exp 1 ^ d := by rw [← mul_pow]; congr 1; ring
      _ = Real.exp (d : ℝ) := by rw [← Real.exp_nat_mul, mul_one]

end FourExpHeight

theorem solution
    (P Q : Polynomial ℤ) (hP : P ≠ 0) (hQP : Q ∣ P) (H : ℝ)
    (hPH : ∀ i : ℕ, |(P.coeff i : ℝ)| ≤ H) :
    ∀ i : ℕ, |(Q.coeff i : ℝ)| ≤ Real.exp (P.natDegree : ℝ) * H := by
  obtain ⟨R, rfl⟩ := hQP
  intro i
  have hR : R ≠ 0 := right_ne_zero_of_mul hP
  have hH0 : 0 ≤ H := (abs_nonneg _).trans (hPH 0)
  set φ : ℤ →+* ℂ := Int.castRingHom ℂ with hφ
  have hinj : Function.Injective φ := Int.cast_injective
  have hmap : (Q * R).map φ = Q.map φ * R.map φ := Polynomial.map_mul φ
  -- `M(R) ≥ 1`
  have hRlc : 1 ≤ ‖(R.map φ).leadingCoeff‖ := by
    rw [leadingCoeff_map_of_injective hinj]
    have h1 : (1 : ℤ) ≤ |R.leadingCoeff| := Int.one_le_abs (leadingCoeff_ne_zero.mpr hR)
    simp only [hφ, eq_intCast, Complex.norm_intCast]
    exact_mod_cast h1
  have hRM := one_le_mahlerMeasure_of_one_le_norm_leadingCoeff hRlc
  -- the coefficient bound through Mahler measure
  have h1 := norm_coeff_le_choose_mul_mahlerMeasure_of_one_le_mahlerMeasure i (Q.map φ) (R.map φ) hRM
  have hcoef : ‖(Q.map φ).coeff i‖ = |(Q.coeff i : ℝ)| := by
    simp [hφ, coeff_map, Complex.norm_intCast]
  have hM := mahlerMeasure_le_sqrt_natDegree_add_one_mul_supNorm (Q.map φ * R.map φ)
  have hsup' : ((Q * R).map φ).supNorm ≤ H := by
    obtain ⟨j, hj⟩ := ((Q * R).map φ).exists_eq_supNorm
    rw [hj, coeff_map]
    simp only [hφ, eq_intCast, Complex.norm_intCast]
    exact hPH j
  have hsup : (Q.map φ * R.map φ).supNorm ≤ H := by
    simpa only [hmap] using hsup'
  have hdegP : (Q.map φ * R.map φ).natDegree = (Q * R).natDegree := by
    rw [← hmap, natDegree_map_eq_of_injective hinj]
  have hdegQ : (Q.map φ).natDegree = Q.natDegree := natDegree_map_eq_of_injective hinj Q
  have hδ : Q.natDegree ≤ (Q * R).natDegree := natDegree_le_of_dvd (dvd_mul_right Q R) hP
  have hfac := FourExpHeight.choose_sqrt_le_exp (Q * R).natDegree Q.natDegree i hδ
  rw [← hcoef]
  calc ‖(Q.map φ).coeff i‖
      ≤ ((Q.map φ).natDegree.choose i : ℝ) * (Q.map φ * R.map φ).mahlerMeasure := h1
    _ ≤ ((Q.natDegree.choose i : ℕ) : ℝ) * (Real.sqrt (((Q * R).natDegree : ℝ) + 1) * H) := by
        rw [hdegQ]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        refine hM.trans ?_
        rw [hdegP]
        exact mul_le_mul_of_nonneg_left hsup (Real.sqrt_nonneg _)
    _ = (((Q.natDegree.choose i : ℕ) : ℝ) * Real.sqrt (((Q * R).natDegree : ℝ) + 1)) * H := by ring
    _ ≤ Real.exp ((Q * R).natDegree : ℝ) * H := mul_le_mul_of_nonneg_right hfac hH0
