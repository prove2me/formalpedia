-- Prove2me | solution 1 for BookProof.ChapterA3.mgamma_conjugation_unique_up_to_scalar
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T00:13:41.708815+00:00
-- url     : https://prove2.me/submissions/f8e613a8-4d91-4ef0-84e8-88c1dc14fc45

-- Generated from ChapterPauliCommutant.lean — solution of BookProof.ChapterA3.mgamma_conjugation_unique_up_to_scalar
import Mathlib
import Definitions.Def_ChapterPauliCommutant
import Theorems.Thm_BookProof_ChapterA3_mgamma_commutant_scalar
import Definitions.Def_ChapterA3
open BookProof.ChapterA3



open Matrix

set_option maxHeartbeats 1000000 in
theorem solution
    {S T : Matrix (Fin 4) (Fin 4) ℂ} (hS : IsUnit S.det) (hT : IsUnit T.det)
    (h : ∀ μ, S * mgamma μ * S⁻¹ = T * mgamma μ * T⁻¹) :
    ∃ c : ℂ, c ≠ 0 ∧ S = c • T := by

  have hTinv : T⁻¹ * T = 1 := Matrix.nonsing_inv_mul T hT
  have hTinv' : T * T⁻¹ = 1 := Matrix.mul_nonsing_inv T hT
  have hSinv : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S hS
  have hcomm : ∀ μ, (T⁻¹ * S) * mgamma μ = mgamma μ * (T⁻¹ * S) := by
    intro μ
    have h1 : S * mgamma μ = T * mgamma μ * T⁻¹ * S := by
      have h2 := congrArg (fun X => X * S) (h μ)
      simp only [Matrix.mul_assoc] at h2 ⊢
      rw [hSinv, Matrix.mul_one] at h2
      simpa [Matrix.mul_assoc] using h2
    calc (T⁻¹ * S) * mgamma μ = T⁻¹ * (S * mgamma μ) := by rw [Matrix.mul_assoc]
      _ = T⁻¹ * (T * mgamma μ * T⁻¹ * S) := by rw [h1]
      _ = mgamma μ * (T⁻¹ * S) := by
          simp only [Matrix.mul_assoc, ← Matrix.mul_assoc T⁻¹ T, hTinv, Matrix.one_mul]
  set c : ℂ := (T⁻¹ * S) 0 0 with hc
  have hU : T⁻¹ * S = c • (1 : Matrix (Fin 4) (Fin 4) ℂ) :=
    mgamma_commutant_scalar _ hcomm
  have hST : S = c • T := by
    have h3 : T * (T⁻¹ * S) = S := by rw [← Matrix.mul_assoc, hTinv', Matrix.one_mul]
    rw [hU] at h3
    rw [← h3]
    simp
  refine ⟨c, ?_, hST⟩
  intro hc0
  rw [hc0, zero_smul] at hST
  rw [hST] at hS
  rw [Matrix.det_zero] at hS
  exact hS.ne_zero rfl
