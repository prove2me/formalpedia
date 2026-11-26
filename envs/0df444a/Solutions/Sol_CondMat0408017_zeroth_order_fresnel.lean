-- Prove2me | solution 1 for CondMat0408017.zeroth_order_fresnel
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-26T17:25:23.451972+00:00
-- url     : https://prove2.me/submissions/545f065e-9bee-47d8-908c-be79cfaf3347

import Mathlib
import Definitions.Def_CondMat0408017_Basic
import Theorems.Thm_CondMat0408017_sapt_matrix_element_expansion

open MeasureTheory Filter Topology Complex CondMat0408017

theorem solution (eps : ℂ) (wv : ℝ) (α α0 : ℝ → ℂ)
    (hα : ∀ q, α q ^ 2 = eps * wv ^ 2 - q ^ 2) (hα0 : ∀ q, α0 q ^ 2 = wv ^ 2 - q ^ 2)
    (heps : eps ≠ 1) (hwv : wv ≠ 0) (R : DKernel) :
    ((∀ q, eps * α0 q + α q ≠ 0) →
      (∀ k, rreNpCoeff 1 0 k k (α k) (α0 k) * R.diag k = rreNpCoeff (-1) 0 k k (α k) (α0 k)) →
      (∀ q k, rreNpCoeff 1 0 q q (α q) (α0 q) * R.reg q k = 0) →
      (∀ k, R.diag k = fresnelP eps (α k) (α0 k)) ∧ ∀ q k, R.reg q k = 0) ∧
    ((∀ q, α0 q + α q ≠ 0) →
      (∀ k, rreNsCoeff 1 0 (α k) (α0 k) * R.diag k = rreNsCoeff (-1) 0 (α k) (α0 k)) →
      (∀ q k, rreNsCoeff 1 0 (α q) (α0 q) * R.reg q k = 0) →
      (∀ k, R.diag k = fresnelS (α k) (α0 k)) ∧ ∀ q k, R.reg q k = 0) := by
  have hzero := (sapt_matrix_element_expansion (fun _ => 0) continuous_const 1 one_pos).2.2
  have heps_ne : eps - 1 ≠ 0 := sub_ne_zero.mpr heps
  have hwv_ne : (wv : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hwv
  constructor
  · intro hden hdiag hreg
    constructor
    · intro k
      have hp := (hzero 1 eps wv k (α k) (α0 k) (Or.inl rfl) (hα k) (hα0 k) heps hwv).1
      have hm := (hzero (-1) eps wv k (α k) (α0 k) (Or.inr rfl) (hα k) (hα0 k) heps hwv).1
      have hk := hdiag k
      rw [hp, hm] at hk
      simp only [one_mul, neg_one_mul, ← sub_eq_add_neg] at hk
      have hne : (eps * α0 k + α k) / (eps - 1) ≠ 0 := div_ne_zero (hden k) heps_ne
      simp only [fresnelP]
      field_simp [hden k, heps_ne] at hk ⊢
      linear_combination hk
    · intro q k
      have hp := (hzero 1 eps wv q (α q) (α0 q) (Or.inl rfl) (hα q) (hα0 q) heps hwv).1
      have hqk := hreg q k
      rw [hp, one_mul] at hqk
      have hne : (eps * α0 q + α q) / (eps - 1) ≠ 0 := div_ne_zero (hden q) heps_ne
      exact (mul_eq_zero.mp hqk).resolve_left hne
  · intro hden hdiag hreg
    constructor
    · intro k
      have hp := (hzero 1 eps wv k (α k) (α0 k) (Or.inl rfl) (hα k) (hα0 k) heps hwv).2
      have hm := (hzero (-1) eps wv k (α k) (α0 k) (Or.inr rfl) (hα k) (hα0 k) heps hwv).2
      have hk := hdiag k
      rw [hp, hm] at hk
      simp only [one_mul, neg_one_mul, ← sub_eq_add_neg] at hk
      have hden_ne : (wv : ℂ) ^ 2 * (eps - 1) ≠ 0 := mul_ne_zero (pow_ne_zero 2 hwv_ne) heps_ne
      simp only [fresnelS]
      field_simp [hden k, hden_ne] at hk ⊢
      linear_combination hk
    · intro q k
      have hp := (hzero 1 eps wv q (α q) (α0 q) (Or.inl rfl) (hα q) (hα0 q) heps hwv).2
      have hqk := hreg q k
      rw [hp, one_mul] at hqk
      have hne : (α0 q + α q) / ((wv : ℂ) ^ 2 * (eps - 1)) ≠ 0 :=
        div_ne_zero (hden q) (mul_ne_zero (pow_ne_zero 2 hwv_ne) heps_ne)
      exact (mul_eq_zero.mp hqk).resolve_left hne
