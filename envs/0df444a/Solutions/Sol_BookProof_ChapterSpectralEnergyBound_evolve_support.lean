-- Prove2me | solution 1 for BookProof.ChapterSpectralEnergyBound.evolve_support
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:43:58.909152+00:00
-- url     : https://prove2.me/submissions/dd6c37b2-34ee-448e-a85d-b64dd47cd8e2

import Mathlib
import Definitions.Def_ChapterSpectralEnergyBound
import Definitions.Def_ChapterBornMeasure
-- Generated from ChapterSpectralEnergyBound.lean — theorem BookProof.ChapterSpectralEnergyBound.evolve_support
open BookProof.ChapterBornMeasure
open BookProof.ChapterSpectralEnergyBound



variable {n : Type*} [Fintype n]
open BookProof.ChapterSpectralEnergyBound in
theorem h44_evolve_apply {n : Type*} [Fintype n] (f : n → ℝ) (t : ℝ) (v : EuclideanSpace ℂ n) (i : n) :
    evolve f t v i = Complex.exp (-Complex.I * (t : ℂ) * (f i : ℂ)) * v i := rfl

open BookProof.ChapterSpectralEnergyBound in
theorem h44_supp {n : Type*} [Fintype n] (f : n → ℝ) (t : ℝ) (v : EuclideanSpace ℂ n) (i : n)
    (h : evolve f t v i ≠ 0) : v i ≠ 0 := by
  intro hv; apply h; rw [h44_evolve_apply, hv, mul_zero]

theorem h44_diag_le {n : Type*} [Fintype n] (f : n → ℝ) (E : ℝ) (v : EuclideanSpace ℂ n)
    (h : ∀ i, v i ≠ 0 → |f i| ≤ E) :
    ‖BookProof.ChapterSpectralEnergyBound.diagOp f v‖ ≤ E * ‖v‖ := by
  by_cases hv : v = 0
  · subst hv
    have : BookProof.ChapterSpectralEnergyBound.diagOp f 0 = 0 := by
      ext i; simp [BookProof.ChapterSpectralEnergyBound.diagOp]
    simp [this]
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra hc; push_neg at hc; exact hv (by ext i; simp [hc i])
  have hE : 0 ≤ E := (abs_nonneg _).trans (h j hj)
  have hsq : ‖BookProof.ChapterSpectralEnergyBound.diagOp f v‖ ^ 2 ≤ (E * ‖v‖) ^ 2 := by
    rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    change ‖(f i : ℂ) * v i‖ ^ 2 ≤ E ^ 2 * ‖v i‖ ^ 2
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs]
    by_cases hvi : v i = 0
    · simp [hvi]
    · have := h i hvi
      have h0 := abs_nonneg (f i)
      gcongr
  have h2 : 0 ≤ E * ‖v‖ := mul_nonneg hE (norm_nonneg _)
  nlinarith [norm_nonneg (BookProof.ChapterSpectralEnergyBound.diagOp f v)]

open BookProof.ChapterSpectralEnergyBound in
theorem h44_norm_evolve {n : Type*} [Fintype n] (f : n → ℝ) (t : ℝ) (v : EuclideanSpace ℂ n) :
    ‖evolve f t v‖ = ‖v‖ := by
  have : ‖evolve f t v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h44_evolve_apply, norm_mul]
    have : ‖Complex.exp (-Complex.I * (t : ℂ) * (f i : ℂ))‖ = 1 := by
      rw [Complex.norm_exp]; simp
    rw [this, one_mul]
  have h1 := norm_nonneg (evolve f t v); have h2 := norm_nonneg v
  nlinarith [sq_nonneg (‖evolve f t v‖ - ‖v‖), sq_nonneg (‖evolve f t v‖ + ‖v‖)]

theorem solution (f : n → ℝ) (t : ℝ) (v : EuclideanSpace ℂ n) (i : n)
    (h : evolve f t v i ≠ 0) : v i ≠ 0 := by
  exact h44_supp f t v i h

