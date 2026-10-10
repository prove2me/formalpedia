-- Prove2me | solution 1 for BMV2017.witness_le_one_of_separable
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T14:36:47.940822+00:00
-- url     : https://prove2.me/submissions/f20734b2-1242-4f96-aac6-82d2eba52f38

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_BMV2017_defs

open Matrix
open scoped Kronecker ComplexOrder
namespace BMV2017

theorem bmv_bloch (ρ : Matrix Qubit Qubit ℂ) (h : PeresTerno.IsDensityMatrix ρ) :
    ∃ a d : ℝ, ∃ b : ℂ, ρ = !![(a : ℂ), b; star b, (d : ℂ)] ∧ 0 ≤ a ∧ 0 ≤ d ∧ a + d = 1 ∧
      b.re ^ 2 + b.im ^ 2 ≤ a * d := by
  obtain ⟨hP, htr⟩ := h
  have hH := hP.isHermitian
  have h0 := hP.diag_nonneg (i := 0)
  have h1 := hP.diag_nonneg (i := 1)
  have hdet := hP.det_nonneg
  have h10 : star (ρ 0 1) = ρ 1 0 := hH.apply 1 0
  rw [Complex.le_def] at h0 h1 hdet
  rw [Matrix.det_fin_two] at hdet
  rw [Matrix.trace_fin_two] at htr
  simp only [Complex.zero_re, Complex.zero_im] at h0 h1 hdet
  refine ⟨(ρ 0 0).re, (ρ 1 1).re, ρ 0 1, ?_, h0.1, h1.1, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j
    · simp [Complex.ext_iff, ← h0.2]
    · simp
    · simp [h10]
    · simp [Complex.ext_iff, ← h1.2]
  · have := congrArg Complex.re htr
    simpa using this
  · rw [← h10] at hdet
    simp only [Complex.sub_re, Complex.mul_re, Complex.star_def, Complex.conj_re,
      Complex.conj_im, ← h0.2, ← h1.2] at hdet
    nlinarith [hdet.1]

theorem bmv_prod_bound (ρ₁ ρ₂ : Matrix Qubit Qubit ℂ) (h₁ : PeresTerno.IsDensityMatrix ρ₁)
    (h₂ : PeresTerno.IsDensityMatrix ρ₂) :
    ‖((ρ₁ ⊗ₖ ρ₂) * (σx ⊗ₖ σz)).trace - ((ρ₁ ⊗ₖ ρ₂) * (σy ⊗ₖ σy)).trace‖ ≤ 1 := by
  rw [← mul_kronecker_mul, ← mul_kronecker_mul, trace_kronecker, trace_kronecker]
  obtain ⟨a₁, d₁, b₁, rfl, ha₁, hd₁, hs₁, hb₁⟩ := bmv_bloch ρ₁ h₁
  obtain ⟨a₂, d₂, b₂, rfl, ha₂, hd₂, hs₂, hb₂⟩ := bmv_bloch ρ₂ h₂
  have hc : (!![(a₁ : ℂ), b₁; star b₁, (d₁ : ℂ)] * σx).trace *
        (!![(a₂ : ℂ), b₂; star b₂, (d₂ : ℂ)] * σz).trace -
      (!![(a₁ : ℂ), b₁; star b₁, (d₁ : ℂ)] * σy).trace *
        (!![(a₂ : ℂ), b₂; star b₂, (d₂ : ℂ)] * σy).trace
      = (((2 * b₁.re) * (a₂ - d₂) - (-2 * b₁.im) * (-2 * b₂.im) : ℝ) : ℂ) := by
    apply Complex.ext <;>
    simp [σx, σy, σz, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_le]
  set x := 2 * b₁.re
  set y := -2 * b₁.im
  set z := a₂ - d₂
  set w := -2 * b₂.im
  have hxy : x ^ 2 + y ^ 2 ≤ 1 := by
    simp only [x, y]; nlinarith [sq_nonneg (a₁ - d₁)]
  have hzw : z ^ 2 + w ^ 2 ≤ 1 := by
    simp only [z, w]; nlinarith [sq_nonneg b₂.re]
  have hL : (x * z - y * w) ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (x * w + y * z), mul_le_mul hxy hzw (by positivity) zero_le_one,
      sq_nonneg x, sq_nonneg y, sq_nonneg z, sq_nonneg w]
  constructor <;> nlinarith [sq_nonneg (x * z - y * w + 1), sq_nonneg (x * z - y * w - 1)]

end BMV2017

open BMV2017

theorem solution (ρ : Matrix (Qubit × Qubit) (Qubit × Qubit) ℂ)
    (hρ : IsSeparable ρ) : witness ρ ≤ 1 := by
  obtain ⟨n, p, ρ₁, ρ₂, hp, hsum, h1, h2, rfl⟩ := hρ
  unfold witness
  rw [Finset.sum_mul, trace_sum, Finset.sum_mul, trace_sum, ← Finset.sum_sub_distrib]
  simp_rw [Matrix.smul_mul, trace_smul, smul_eq_mul, ← mul_sub]
  calc ‖∑ i, (p i : ℂ) * (((ρ₁ i ⊗ₖ ρ₂ i) * (σx ⊗ₖ σz)).trace
            - ((ρ₁ i ⊗ₖ ρ₂ i) * (σy ⊗ₖ σy)).trace)‖
      ≤ ∑ i, ‖(p i : ℂ) * (((ρ₁ i ⊗ₖ ρ₂ i) * (σx ⊗ₖ σz)).trace
            - ((ρ₁ i ⊗ₖ ρ₂ i) * (σy ⊗ₖ σy)).trace)‖ := norm_sum_le _ _
    _ ≤ ∑ i, p i * 1 := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp i)]
        exact mul_le_mul_of_nonneg_left (bmv_prod_bound _ _ (h1 i) (h2 i)) (hp i)
    _ = 1 := by simp [hsum]
