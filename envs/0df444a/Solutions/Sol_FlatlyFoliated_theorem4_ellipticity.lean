-- Prove2me | solution 1 for FlatlyFoliated.theorem4_ellipticity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T09:27:59.18898+00:00
-- url     : https://prove2.me/submissions/8ecc72cd-8ee8-4f18-b8cc-2404c84d9b89

import Mathlib
import Definitions.Def_FlatlyFoliatedRelativity_basic


open scoped ContDiff
open FlatlyFoliated

namespace FFT4

lemma normsq (ν : R3) : ‖ν‖ ^ 2 = ∑ a, ν a ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => by positivity))]
  simp [Real.norm_eq_abs, sq_abs]

lemma cs (Q : Fin 3 → Fin 3 → ℝ) (ν : R3) :
    (∑ a, ∑ b, Q a b * ν a * ν b) ^ 2 ≤ (∑ a, ∑ b, Q a b ^ 2) * (∑ a, ν a ^ 2) ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 3 × Fin 3))
    (fun p => Q p.1 p.2) (fun p => ν p.1 * ν p.2)
  simp only [← Finset.univ_product_univ, Finset.sum_product] at h
  have e : ∑ a, ∑ b, (ν a * ν b) ^ 2 = (∑ a, ν a ^ 2) ^ 2 := by
    rw [sq (∑ a, ν a ^ 2), Finset.sum_mul_sum]
    exact Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by ring))
  rw [e] at h
  calc (∑ a, ∑ b, Q a b * ν a * ν b) ^ 2 = (∑ a, ∑ b, Q a b * (ν a * ν b)) ^ 2 := by
        congr 1; exact Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by ring))
    _ ≤ _ := h

lemma ell_eq (f : R3 → ℝ) (ζ : R3 → R3) (x ν : R3) :
    ∑ a, ∑ b, ellCoeff f ζ a b x * ν a * ν b =
      lap f x * ∑ a, ν a ^ 2 - ∑ a, ∑ b, Qmat f ζ a b x * ν a * ν b := by
  simp only [ellCoeff, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl (fun a _ => by ring)

end FFT4

open FFT4 in
theorem solution (Λ : ℝ) (hΛ : 0 < Λ) (μ : R3 → ℝ) (J : R3 → R3)
    (f : R3 → ℝ) (ζ : R3 → R3) (η : R3 → ℝ) (hμ : ContDiff ℝ ∞ μ) (hJ : ContDiff ℝ ∞ J)
    (hf : ContDiff ℝ ∞ f) (hζ : ContDiff ℝ ∞ ζ) (hη : ContDiff ℝ ∞ η)
    (hμnn : ∀ x, 0 ≤ μ x) (hηpos : ∀ x, 0 < η x) (hconv : ∀ x, 0 < lap f x / η x)
    (hsys : EllipticSystem Λ μ J f ζ η) :
    (∀ (x ν : R3), ν ≠ 0 → 0 < ∑ a, ∑ b, ellCoeff f ζ a b x * ν a * ν b) ∧
    (∀ ηmin Qmax : ℝ, 0 < ηmin → (∀ x, ηmin ≤ η x) →
      (∀ (x ν : R3), ‖ν‖ = 1 → |∑ a, ∑ b, Qmat f ζ a b x * ν a * ν b| ≤ Qmax) →
      ∀ (x ν : R3), ‖ν‖ = 1 →
        Real.sqrt (Qmax ^ 2 + 2 * Λ * ηmin ^ 2) - Qmax ≤
          ∑ a, ∑ b, ellCoeff f ζ a b x * ν a * ν b) := by
  -- pointwise facts
  have key : ∀ x, 2 * Λ * η x ^ 2 + ∑ a, ∑ b, Qmat f ζ a b x ^ 2 ≤ lap f x ^ 2 := by
    intro x
    have h := hsys.1 x
    have := hμnn x
    have := Real.pi_pos
    have : 0 ≤ 16 * Real.pi * μ x * η x ^ 2 := by positivity
    nlinarith
  have hL : ∀ x, 0 < lap f x := fun x => by
    have := hconv x
    rwa [div_pos_iff_of_pos_right (hηpos x)] at this
  refine ⟨fun x ν hν => ?_, fun ηmin Qmax hηmin hmin hQ x ν hν => ?_⟩
  · rw [ell_eq]
    set N := ∑ a, ν a ^ 2
    set q := ∑ a, ∑ b, Qmat f ζ a b x * ν a * ν b
    set S := ∑ a, ∑ b, Qmat f ζ a b x ^ 2
    have hN : 0 < N := by
      have e : ‖ν‖ ^ 2 = N := normsq ν
      rw [← e]; exact pow_pos (norm_pos_iff.mpr hν) 2
    have hcs : q ^ 2 ≤ S * N ^ 2 := cs _ ν
    have hk := key x
    have hη2 : 0 < η x ^ 2 := by have := hηpos x; positivity
    have hlt : q ^ 2 < (lap f x * N) ^ 2 := by
      have : S < lap f x ^ 2 := by nlinarith
      have : S * N ^ 2 < lap f x ^ 2 * N ^ 2 := mul_lt_mul_of_pos_right this (by positivity)
      nlinarith
    have hLN : 0 < lap f x * N := mul_pos (hL x) hN
    have := abs_lt_of_sq_lt_sq hlt hLN.le
    rw [abs_lt] at this
    linarith
  · rw [ell_eq]
    have hN : ∑ a, ν a ^ 2 = 1 := by rw [← normsq, hν, one_pow]
    rw [hN, mul_one]
    have hqQ := hQ x ν hν
    rw [abs_le] at hqQ
    set q := ∑ a, ∑ b, Qmat f ζ a b x * ν a * ν b
    set S := ∑ a, ∑ b, Qmat f ζ a b x ^ 2
    set L := lap f x
    set c := 2 * Λ * ηmin ^ 2
    have hcs : q ^ 2 ≤ S := by have := cs (fun a b => Qmat f ζ a b x) ν; rw [hN] at this; simpa using this
    have hQ0 : 0 ≤ Qmax := by linarith
    have hc : 0 ≤ c := by positivity
    have hηx : ηmin ^ 2 ≤ η x ^ 2 := by have := hmin x; nlinarith
    have hk := key x
    have hL2 : q ^ 2 + c ≤ L ^ 2 := by nlinarith
    set A := Real.sqrt (Qmax ^ 2 + c)
    set B := Real.sqrt (q ^ 2 + c)
    have hA : A ^ 2 = Qmax ^ 2 + c := Real.sq_sqrt (by positivity)
    have hB : B ^ 2 = q ^ 2 + c := Real.sq_sqrt (by positivity)
    have hA0 : 0 ≤ A := Real.sqrt_nonneg _
    have hB0 : 0 ≤ B := Real.sqrt_nonneg _
    have hBL : B ≤ L := by
      rw [show B = Real.sqrt (q ^ 2 + c) from rfl, Real.sqrt_le_left (hL x).le]
      exact hL2
    have hAq : A * q ≤ B * Qmax := by
      rcases le_or_gt q 0 with h | h
      · nlinarith
      · have h1 : (A * q) ^ 2 ≤ (B * Qmax) ^ 2 := by
          have hq2 : q ^ 2 ≤ Qmax ^ 2 := by nlinarith
          rw [mul_pow, mul_pow, hA, hB]; nlinarith [mul_le_mul_of_nonneg_left hq2 hc]
        exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp h1
    have hAQ : Qmax ≤ A := by
      rw [show A = Real.sqrt (Qmax ^ 2 + c) from rfl]
      exact Real.le_sqrt_of_sq_le (by linarith)
    have hsq : (A + q) ^ 2 ≤ (B + Qmax) ^ 2 := by nlinarith
    have h2 : A + q ≤ B + Qmax := by
      exact (pow_le_pow_iff_left₀ (by linarith) (by positivity) two_ne_zero).mp hsq
    linarith
