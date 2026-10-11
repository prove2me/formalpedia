-- Prove2me | solution 1 for BookProof.ChapterA3.mgamma_conj_eq_self_iff
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:04:21.495567+00:00
-- url     : https://prove2.me/submissions/abc86ef0-350d-437e-84a2-5b6725990c50

-- Generated from ChapterPauliCommutant.lean — solution of BookProof.ChapterA3.mgamma_conj_eq_self_iff
import Mathlib
import Definitions.Def_ChapterPauliCommutant
import Theorems.Thm_BookProof_ChapterA3_mgamma_conjugation_unique_up_to_scalar
import Definitions.Def_ChapterA3
open BookProof.ChapterA3



open Matrix

set_option maxHeartbeats 1000000 in
theorem solution {S : Matrix (Fin 4) (Fin 4) ℂ} (hS : IsUnit S.det) :
    (∀ μ, S * mgamma μ * S⁻¹ = mgamma μ) ↔
      ∃ c : ℂ, c ≠ 0 ∧ S = c • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by

  constructor
  · intro h
    have hone : IsUnit (1 : Matrix (Fin 4) (Fin 4) ℂ).det := by simp
    refine (mgamma_conjugation_unique_up_to_scalar hS hone ?_).imp ?_
    · intro μ; simpa using h μ
    · intro c hc; exact ⟨hc.1, by simpa using hc.2⟩
  · rintro ⟨c, hc, rfl⟩ μ
    have hcinv : (c • (1 : Matrix (Fin 4) (Fin 4) ℂ))⁻¹ = c⁻¹ • 1 :=
      Matrix.inv_eq_right_inv (by
        rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul,
          mul_inv_cancel₀ hc, one_smul])
    rw [hcinv]
    simp [smul_smul, mul_comm, mul_inv_cancel₀ hc]
