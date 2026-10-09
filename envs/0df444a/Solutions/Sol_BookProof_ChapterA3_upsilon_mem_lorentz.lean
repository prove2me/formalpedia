-- Prove2me | solution 1 for BookProof.ChapterA3.upsilon_mem_lorentz
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:34:16.38998+00:00
-- url     : https://prove2.me/submissions/19f933f6-fc6c-4315-9a0f-bf5ab22a2331

-- Generated from ChapterA3h.lean — solution of BookProof.ChapterA3.upsilon_mem_lorentz
import Mathlib
import Definitions.Def_ChapterA3h
import Theorems.Thm_BookProof_ChapterA3_upsilon_metric
open BookProof.ChapterA3



open Matrix
open scoped ComplexConjugate

set_option maxHeartbeats 1000000 in
theorem solution (T : Matrix (Fin 2) (Fin 2) ℂ) (hT : T.det = 1) :
    Upsilon T ∈ LorentzO := by

  -- From(Note 47, proof): `upsilon_metric T hT : Λᵀ * η * Λ = η`. Let `η := minkowskiMat`.
  set η := minkowskiMat
  have hη2 : η * η = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [η, minkowskiMat, minkowskiR, minkowskiZ, Matrix.mul_apply]
  have h : (Upsilon T)ᵀ * η * Upsilon T = η := upsilon_metric T hT
  generalize_proofs at *
  have h_mul : (η * (Upsilon T)ᵀ * η) * Upsilon T = 1 := by
    simp_all [Matrix.mul_assoc]
  have h_mul_comm : Upsilon T * (η * (Upsilon T)ᵀ * η) = 1 := by
    rw [← mul_eq_one_comm, h_mul]
  apply_fun (fun x => x * η) at h_mul_comm
  simp_all only [Matrix.mul_assoc, mul_one, one_mul]
  exact funext fun i => funext fun j => by
    simpa [Matrix.mul_assoc] using congr_fun (congr_fun h_mul_comm i) j
