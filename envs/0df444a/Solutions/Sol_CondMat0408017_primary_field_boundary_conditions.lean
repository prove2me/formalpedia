-- Prove2me | solution 1 for CondMat0408017.primary_field_boundary_conditions
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-26T17:22:22.623986+00:00
-- url     : https://prove2.me/submissions/e5cb3df6-d526-48ce-93a7-aa9f2fe1e45b

import Mathlib
import Definitions.Def_CondMat0408017_Basic

open MeasureTheory Filter Topology Complex CondMat0408017

theorem solution (ν : Polarization) (ω : ℝ) (hω : ω ≠ 0)
    (κP κM : ℂ) (hκP : κP ≠ 0) (hκM : κM ≠ 0) (dζ : ℝ) (ΦP d1P d3P ΦM d1M d3M : ℂ) :
    (crossProduct (surfaceNormal dζ)
          ((emFields ν ω κM ΦM d1M d3M).1 - (emFields ν ω κP ΦP d1P d3P).1) = 0 ∧
        crossProduct (surfaceNormal dζ)
          ((emFields ν ω κM ΦM d1M d3M).2 - (emFields ν ω κP ΦP d1P d3P).2) = 0) ↔
      (ΦP = ΦM ∧ normalDeriv dζ d1P d3P / κP = normalDeriv dζ d1M d3M / κM) := by
  have hs_pos : 0 < Real.sqrt (1 + dζ ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hs_ne : (Real.sqrt (1 + dζ ^ 2) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs_pos.ne'
  have hωc : (ω : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hω
  cases ν
  · -- p-polarization
    simp only [emFields, surfaceNormal, normalDeriv, crossProduct, LinearMap.mk₂_apply,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul, funext_iff, Pi.zero_apply]
    constructor
    · rintro ⟨hE, hH⟩
      have h1 := hE 1
      have h2 := hH 0
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons] at h1 h2
      constructor
      · have : ΦM - ΦP = 0 := by
          have h2' : (Real.sqrt (1 + dζ ^ 2) : ℂ)⁻¹ * (-(ΦM - ΦP)) = 0 := by
            linear_combination h2
          rcases mul_eq_zero.mp h2' with hinv | hsub
          · exact absurd (inv_eq_zero.mp hinv) hs_ne
          · exact neg_eq_zero.mp hsub
        exact (sub_eq_zero.mp this).symm
      · have h1' : (Real.sqrt (1 + dζ ^ 2) : ℂ)⁻¹ * (I / (ω : ℂ)) *
            ((-(dζ : ℂ) * d1P + d3P) / κP - (-(dζ : ℂ) * d1M + d3M) / κM) = 0 := by
          have : (Real.sqrt (1 + dζ ^ 2) : ℂ)⁻¹ * (I / (ω : ℂ)) *
              ((-(dζ : ℂ) * d1P + d3P) / κP - (-(dζ : ℂ) * d1M + d3M) / κM) =
              (Real.sqrt (1 + dζ ^ 2) : ℂ)⁻¹ * 1 * (-(I / ((ω : ℂ) * κM)) * d3M - -(I / ((ω : ℂ) * κP)) * d3P) -
              (Real.sqrt (1 + dζ ^ 2) : ℂ)⁻¹ * -(dζ : ℂ) * (I / ((ω : ℂ) * κM) * d1M - I / ((ω : ℂ) * κP) * d1P) := by
            field_simp [hωc, hκP, hκM, hs_ne]
            ring
          rw [this]
          exact h1
        have hfac : (Real.sqrt (1 + dζ ^ 2) : ℂ)⁻¹ * (I / (ω : ℂ)) ≠ 0 :=
          mul_ne_zero (inv_ne_zero hs_ne) (div_ne_zero I_ne_zero hωc)
        have hdiff : (-(dζ : ℂ) * d1P + d3P) / κP - (-(dζ : ℂ) * d1M + d3M) / κM = 0 :=
          (mul_eq_zero.mp h1').resolve_left hfac
        have heq := sub_eq_zero.mp hdiff
        field_simp [hs_ne, hκP, hκM] at heq ⊢
        linear_combination heq
    · rintro ⟨hΦ, hnd⟩
      have hnd' : (-(dζ : ℂ) * d1P + d3P) / κP = (-(dζ : ℂ) * d1M + d3M) / κM := by
        field_simp [hs_ne, hκP, hκM] at hnd ⊢
        linear_combination hnd
      constructor <;> intro i <;> fin_cases i <;> dsimp
      · ring
      · field_simp [hs_ne, hωc, hκP, hκM] at hnd' ⊢
        linear_combination I * hnd'
      · ring
      · rw [hΦ]; ring
      · ring
      · rw [hΦ]; ring
  · -- s-polarization
    simp only [emFields, surfaceNormal, normalDeriv, crossProduct, LinearMap.mk₂_apply,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul, funext_iff, Pi.zero_apply]
    constructor
    · rintro ⟨hE, hH⟩
      have h2 := hE 0
      have h1 := hH 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons] at h1 h2
      constructor
      · have : ΦM - ΦP = 0 := by
          have h2' : (Real.sqrt (1 + dζ ^ 2) : ℂ)⁻¹ * (-(ΦM - ΦP)) = 0 := by
            linear_combination h2
          rcases mul_eq_zero.mp h2' with hinv | hsub
          · exact absurd (inv_eq_zero.mp hinv) hs_ne
          · exact neg_eq_zero.mp hsub
        exact (sub_eq_zero.mp this).symm
      · have h1' : (Real.sqrt (1 + dζ ^ 2) : ℂ)⁻¹ * (I / (ω : ℂ)) *
            ((-(dζ : ℂ) * d1M + d3M) / κM - (-(dζ : ℂ) * d1P + d3P) / κP) = 0 := by
          have : (Real.sqrt (1 + dζ ^ 2) : ℂ)⁻¹ * (I / (ω : ℂ)) *
              ((-(dζ : ℂ) * d1M + d3M) / κM - (-(dζ : ℂ) * d1P + d3P) / κP) =
              (Real.sqrt (1 + dζ ^ 2) : ℂ)⁻¹ * 1 * (I / ((ω : ℂ) * κM) * d3M - I / ((ω : ℂ) * κP) * d3P) -
              (Real.sqrt (1 + dζ ^ 2) : ℂ)⁻¹ * -(dζ : ℂ) * (-(I / ((ω : ℂ) * κM)) * d1M - -(I / ((ω : ℂ) * κP)) * d1P) := by
            field_simp [hωc, hκP, hκM, hs_ne]
            ring
          rw [this]
          exact h1
        have hfac : (Real.sqrt (1 + dζ ^ 2) : ℂ)⁻¹ * (I / (ω : ℂ)) ≠ 0 :=
          mul_ne_zero (inv_ne_zero hs_ne) (div_ne_zero I_ne_zero hωc)
        have hdiff : (-(dζ : ℂ) * d1M + d3M) / κM - (-(dζ : ℂ) * d1P + d3P) / κP = 0 :=
          (mul_eq_zero.mp h1').resolve_left hfac
        have heq := (sub_eq_zero.mp hdiff).symm
        field_simp [hs_ne, hκP, hκM] at heq ⊢
        linear_combination heq
    · rintro ⟨hΦ, hnd⟩
      have hnd' : (-(dζ : ℂ) * d1P + d3P) / κP = (-(dζ : ℂ) * d1M + d3M) / κM := by
        field_simp [hs_ne, hκP, hκM] at hnd ⊢
        linear_combination hnd
      constructor <;> intro i <;> fin_cases i <;> dsimp
      · rw [hΦ]; ring
      · ring
      · rw [hΦ]; ring
      · ring
      · field_simp [hs_ne, hωc, hκP, hκM] at hnd' ⊢
        linear_combination -I * hnd'
      · ring
