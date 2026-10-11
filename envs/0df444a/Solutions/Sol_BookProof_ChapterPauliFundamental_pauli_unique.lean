-- Prove2me | solution 1 for BookProof.ChapterPauliFundamental.pauli_unique
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:04:26.372871+00:00
-- url     : https://prove2.me/submissions/291998ad-3d82-4b23-b99f-69484df6ea14

-- Generated from ChapterPauliFundamental.lean — solution of BookProof.ChapterPauliFundamental.pauli_unique
import Mathlib
import Definitions.Def_ChapterPauliFundamental
import Theorems.Thm_BookProof_ChapterPauliFundamental_exists_intertwiner
import Theorems.Thm_BookProof_ChapterGammaCommutant_gamma_commutant_scalar
import Definitions.Def_ChapterGammaCommutant
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3b
open BookProof.ChapterPauliFundamental



open Matrix Finset


open BookProof.ChapterA3 BookProof.ChapterGammaCommutant

variable {A : Fin 4 → M4}

set_option maxHeartbeats 1000000 in
theorem solution {B : Fin 4 → M4} (hA : IsCliffordC A)
    (S T : M4) (hS : IsUnit S.det) (hT : IsUnit T.det)
    (hSeq : ∀ μ, B μ = S * A μ * S⁻¹) (hTeq : ∀ μ, B μ = T * A μ * T⁻¹) :
    ∃ c : ℂ, c ≠ 0 ∧ T = c • S := by

  obtain ⟨P, hP, hPeq⟩ := exists_intertwiner hA
  have hSS : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul _ hS
  have hSS' : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv _ hS
  have hTT : T⁻¹ * T = 1 := Matrix.nonsing_inv_mul _ hT
  have hPP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ hP
  have hPP' : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ hP
  -- `X = S⁻¹ T` commutes with the Clifford set `A`
  set X : M4 := S⁻¹ * T with hX
  have hcomm : ∀ μ, X * A μ = A μ * X := by
    intro μ
    have h1 : S * A μ * S⁻¹ = T * A μ * T⁻¹ := by rw [← hSeq μ, ← hTeq μ]
    have e1 : S⁻¹ * (S * A μ * S⁻¹) * T = (S⁻¹ * S) * A μ * (S⁻¹ * T) := by
      simp only [Matrix.mul_assoc]
    have e2 : S⁻¹ * (T * A μ * T⁻¹) * T = (S⁻¹ * T) * A μ * (T⁻¹ * T) := by
      simp only [Matrix.mul_assoc]
    have h2 := congrArg (fun Y : M4 => S⁻¹ * Y * T) h1
    rw [e1, e2, hSS, hTT, Matrix.one_mul, Matrix.mul_one] at h2
    rw [hX, ← h2]
  -- transport to the concrete model, where the commutant is scalar
  set Y : M4 := P⁻¹ * X * P with hY
  have hYcomm : ∀ μ, Y * mgamma μ = mgamma μ * Y := by
    intro μ
    have hg : mgamma μ = P⁻¹ * A μ * P := by
      rw [hPeq μ]
      have e : P⁻¹ * (P * mgamma μ * P⁻¹) * P = (P⁻¹ * P) * mgamma μ * (P⁻¹ * P) := by
        simp only [Matrix.mul_assoc]
      rw [e, hPP, Matrix.one_mul, Matrix.mul_one]
    rw [hY, hg]
    have e1 : (P⁻¹ * X * P) * (P⁻¹ * A μ * P) = P⁻¹ * X * (P * P⁻¹) * A μ * P := by
      simp only [Matrix.mul_assoc]
    have e2 : (P⁻¹ * A μ * P) * (P⁻¹ * X * P) = P⁻¹ * A μ * (P * P⁻¹) * X * P := by
      simp only [Matrix.mul_assoc]
    rw [e1, e2, hPP', Matrix.mul_one, Matrix.mul_one]
    rw [Matrix.mul_assoc P⁻¹ X (A μ), hcomm μ, ← Matrix.mul_assoc]
  obtain ⟨c, hc⟩ : ∃ c : ℂ, Y = c • (1 : M4) := ⟨Y 0 0, gamma_commutant_scalar Y hYcomm⟩
  have hXc : X = c • (1 : M4) := by
    have hXeq : P * Y * P⁻¹ = X := by
      rw [hY]
      have e : P * (P⁻¹ * X * P) * P⁻¹ = (P * P⁻¹) * X * (P * P⁻¹) := by
        simp only [Matrix.mul_assoc]
      rw [e, hPP', Matrix.one_mul, Matrix.mul_one]
    rw [← hXeq, hc, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hPP']
  have hTc : T = c • S := by
    have hSX : S * X = T := by rw [hX, ← Matrix.mul_assoc, hSS', Matrix.one_mul]
    rw [← hSX, hXc, Matrix.mul_smul, Matrix.mul_one]
  refine ⟨c, ?_, hTc⟩
  rintro rfl
  rw [zero_smul] at hTc
  rw [hTc, Matrix.det_zero] at hT
  exact not_isUnit_zero hT
