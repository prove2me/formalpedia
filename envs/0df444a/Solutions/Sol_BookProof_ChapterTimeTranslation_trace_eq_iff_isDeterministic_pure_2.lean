-- Prove2me | solution 2 for BookProof.ChapterTimeTranslation.trace_eq_iff_isDeterministic_pure
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T07:00:41.724987+00:00
-- url     : https://prove2.me/submissions/7fd3dee2-5bd8-4f40-a984-1bdd47845eda

import Mathlib
import Definitions.Def_ChapterTimeTranslation
import Definitions.Def_ChapterReconstruct
import Theorems.Thm_BookProof_ChapterTimeTranslation_trace_eq_iff_isDeterministic
-- Generated from ChapterTimeTranslation.lean — theorem BookProof.ChapterTimeTranslation.trace_eq_iff_isDeterministic_pure
open BookProof.ChapterReconstruct
open BookProof.ChapterTimeTranslation


open scoped BigOperators
open Finset Matrix
open BookProof.ChapterReconstruct


variable {n : ℕ}
open BookProof.ChapterTimeTranslation in
theorem h44_rho_smul {n : ℕ} (c : ℝ) (Ψ : Fin n → ℂ) :
    rho ((c : ℂ) • Ψ) = ((c ^ 2 : ℝ) : ℂ) • rho Ψ := by
  ext i j; simp [rho, Complex.conj_ofReal]; ring

open BookProof.ChapterTimeTranslation in
theorem h44_diag_smul {n : ℕ} (c : ℂ) (M : Matrix (Fin n) (Fin n) ℂ) :
    diagPart (c • M) = c • diagPart M := by
  ext i j; by_cases h : i = j <;> simp [diagPart, h]

theorem solution (U : Matrix (Fin n) (Fin n) ℂ) :
    (∀ (a : Fin n) (Ψ : Fin n → ℂ), (∑ k : Fin n, ‖Ψ k‖ ^ 2) = 1 →
        (diagPart (rho Ψ) * measOp U a).trace = (rho Ψ * measOp U a).trace)
      ↔ IsDeterministic U := by
  rw [← BookProof.ChapterTimeTranslation.trace_eq_iff_isDeterministic]
  constructor
  · intro h a Ψ
    set r : ℝ := Real.sqrt (∑ k : Fin n, ‖Ψ k‖ ^ 2) with hr
    by_cases h0 : r = 0
    · have hΨ : Ψ = 0 := by
        have hs : ∑ k : Fin n, ‖Ψ k‖ ^ 2 = 0 := by
          have := Real.sqrt_eq_zero (Finset.sum_nonneg fun k _ => sq_nonneg ‖Ψ k‖) |>.mp h0.symm.symm
          exact this
        funext k
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg ‖Ψ k‖)).mp hs k (Finset.mem_univ _)
        simpa using this
      subst hΨ
      have : rho (0 : Fin n → ℂ) = 0 := by ext i j; simp [rho]
      have hd : diagPart (0 : Matrix (Fin n) (Fin n) ℂ) = 0 := by ext i j; simp [diagPart]
      rw [this, hd]
    · have hrpos : 0 < r := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm h0)
      set φ : Fin n → ℂ := ((r⁻¹ : ℝ) : ℂ) • Ψ
      have hφ : ∑ k : Fin n, ‖φ k‖ ^ 2 = 1 := by
        simp only [φ, Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_inv, abs_of_pos hrpos, mul_pow, ← Finset.mul_sum]
        rw [inv_pow, ← Real.sq_sqrt (Finset.sum_nonneg fun k _ => sq_nonneg ‖Ψ k‖), ← hr]
        exact inv_mul_cancel₀ (pow_ne_zero 2 h0)
      have hΨφ : Ψ = ((r : ℝ) : ℂ) • φ := by
        simp only [φ, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ h0, Complex.ofReal_one, one_smul]
      have := h a φ hφ
      rw [hΨφ, h44_rho_smul, h44_diag_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.trace_smul,
        Matrix.trace_smul, this]
  · intro h a Ψ _
    exact h a Ψ

