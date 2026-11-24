-- Prove2me | solution 1 for ConjGrad.ErrorDecrease.Supplement.theorem_4_4
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T09:59:33.478213+00:00
-- url     : https://prove2.me/submissions/56223f9b-3aaa-4e26-8aea-0afc7f22b698

import Mathlib
import Definitions.Def_ConjGrad_ErrorDecrease_errorFun
import Definitions.Def_ConjGrad_ErrorDecrease_rayleigh

open Matrix ConjGrad.ErrorDecrease

theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k h : Fin n → ℝ) (hh : A *ᵥ h = k) (x : Fin n → ℝ) :
    ((k - A *ᵥ x) ⬝ᵥ (k - A *ᵥ x)) / rayleigh A (k - A *ᵥ x) ≤ errorFun A h x ∧
    errorFun A h x ≤ ((k - A *ᵥ x) ⬝ᵥ (k - A *ᵥ x)) / rayleigh A (h - x) ∧
    rayleigh A (h - x) ≤ rayleigh A (k - A *ᵥ x) ∧
    Real.sqrt ((k - A *ᵥ x) ⬝ᵥ (k - A *ᵥ x)) / rayleigh A (k - A *ᵥ x) ≤
      Real.sqrt ((h - x) ⬝ᵥ (h - x)) ∧
    Real.sqrt ((h - x) ⬝ᵥ (h - x)) ≤
      Real.sqrt ((k - A *ᵥ x) ⬝ᵥ (k - A *ᵥ x)) / rayleigh A (h - x) := by
  classical
  set y := h - x with hy
  set r := k - A *ᵥ x with hr
  have hrAy : r = A *ᵥ y := by
    simp only [r, y, mulVec_sub, hh]
  have hsymm : A.transpose = A := (isHermitian_iff_isSymm.mp hA.1).eq
  have hsymm_form (u v : Fin n → ℝ) : u ⬝ᵥ (A *ᵥ v) = v ⬝ᵥ (A *ᵥ u) := by
    have := dotProduct_transpose_mulVec A u v
    simpa [hsymm] using this
  have hnonneg (u : Fin n → ℝ) : 0 ≤ u ⬝ᵥ (A *ᵥ u) := by
    simpa using hA.posSemidef.dotProduct_mulVec_nonneg u
  -- Cauchy–Schwarz for the A-bilinear form, via the discriminant.
  have csA (u v : Fin n → ℝ) :
      (u ⬝ᵥ (A *ᵥ v)) ^ 2 ≤ (u ⬝ᵥ (A *ᵥ u)) * (v ⬝ᵥ (A *ᵥ v)) := by
    by_cases hv : v ⬝ᵥ (A *ᵥ v) = 0
    · have hv0 : v = 0 := by
        by_contra hne
        have := hA.dotProduct_mulVec_pos hne
        exact (ne_of_gt (by simpa using this)) hv
      simp [hv0]
    · have hvpos : 0 < v ⬝ᵥ (A *ᵥ v) := lt_of_le_of_ne (hnonneg v) (Ne.symm hv)
      set t := (u ⬝ᵥ (A *ᵥ v)) / (v ⬝ᵥ (A *ᵥ v)) with ht_def
      have hkey := hnonneg (u - t • v)
      have hexpand : (u - t • v) ⬝ᵥ (A *ᵥ (u - t • v)) =
          (u ⬝ᵥ (A *ᵥ u)) - 2 * t * (u ⬝ᵥ (A *ᵥ v)) + t ^ 2 * (v ⬝ᵥ (A *ᵥ v)) := by
        simp only [mulVec_sub, mulVec_smul, sub_dotProduct, dotProduct_sub, smul_dotProduct,
          dotProduct_smul, smul_eq_mul, hsymm_form]
        ring
      rw [hexpand, ht_def] at hkey
      field_simp [hv] at hkey
      nlinarith
  -- Ordinary Cauchy–Schwarz for dotProduct.
  have csStd (u v : Fin n → ℝ) : (u ⬝ᵥ v) ^ 2 ≤ (u ⬝ᵥ u) * (v ⬝ᵥ v) := by
    simpa [dotProduct, sq] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u v
  simp only [rayleigh, errorFun, ← hy, ← hrAy]
  by_cases hy0 : y = 0
  · simp [hy0, hrAy]
  · set a := y ⬝ᵥ r with ha
    set b := y ⬝ᵥ y with hb
    set c := r ⬝ᵥ r with hc
    set d := r ⬝ᵥ (A *ᵥ r) with hd
    have hrne : r ≠ 0 := by
      intro hr0
      apply hy0
      apply mulVec_injective_of_isUnit hA.isUnit
      rw [← hrAy, hr0]
      simp
    have norm_pos (v : Fin n → ℝ) (hv : v ≠ 0) : 0 < v ⬝ᵥ v := by
      have hsum : v ⬝ᵥ v = ∑ i : Fin n, v i ^ 2 := by simp [dotProduct, sq]
      rw [hsum]
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
      exact lt_of_lt_of_le (sq_pos_iff.mpr hi)
        (Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i))
    have ha0 : 0 < a := by simpa [a, ← hrAy] using hA.dotProduct_mulVec_pos hy0
    have hb0 : 0 < b := by simpa [b] using norm_pos y hy0
    have hc0 : 0 < c := by simpa [c] using norm_pos r hrne
    have hd0 : 0 < d := by simpa [d] using hA.dotProduct_mulVec_pos hrne
    have c1 : c ^ 2 ≤ a * d := by
      have := csA r y
      rw [← hrAy, ← ha] at this
      nlinarith
    have c2 : a ^ 2 ≤ b * c := by
      have := csStd y r
      rw [← ha] at this
      exact this
    have hsqrt : a ≤ Real.sqrt b * Real.sqrt c := by
      calc a ≤ Real.sqrt (b * c) := Real.le_sqrt_of_sq_le c2
        _ = Real.sqrt b * Real.sqrt c := by rw [Real.sqrt_mul (le_of_lt hb0)]
    have hc3 : c ^ 3 ≤ b * d ^ 2 := by
      have hsq : c ^ 2 * c ^ 2 ≤ (a * d) * (a * d) := mul_self_le_mul_self (by positivity) c1
      have hchain : c * c ^ 3 ≤ c * (b * d ^ 2) := by
        calc c * c ^ 3 = c ^ 2 * c ^ 2 := by ring
          _ ≤ (a * d) * (a * d) := hsq
          _ = a ^ 2 * d ^ 2 := by ring
          _ ≤ (b * c) * d ^ 2 := mul_le_mul_of_nonneg_right c2 (sq_nonneg d)
          _ = c * (b * d ^ 2) := by ring
      exact le_of_mul_le_mul_left hchain (by positivity)
    constructor
    · -- c / (d / c) ≤ a
      field_simp [hc0.ne', hd0.ne']
      nlinarith
    · constructor
      · -- a ≤ c / (a / b)
        field_simp [ha0.ne', hb0.ne']
        nlinarith
      · constructor
        · -- a / b ≤ d / c
          field_simp [hb0.ne', hc0.ne']
          nlinarith [mul_pos ha0 hc0, mul_pos ha0 hd0, mul_pos hb0 hc0]
        · constructor
          · -- sqrt c / (d / c) ≤ sqrt b
            rw [Real.le_sqrt' (by positivity)]
            field_simp [hd0.ne']
            rw [Real.sq_sqrt (le_of_lt hc0)]
            nlinarith [hc3]
          · -- sqrt b ≤ sqrt c / (a / b)
            field_simp [ha0.ne', hb0.ne']
            nlinarith [hsqrt, Real.mul_self_sqrt (le_of_lt hb0), Real.sqrt_nonneg b,
              Real.sqrt_nonneg c]
