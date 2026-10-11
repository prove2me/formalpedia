-- Prove2me | solution 1 for BookProof.ChapterWignerLittleGroup.littleGroup_conj
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T18:00:28.649998+00:00
-- url     : https://prove2.me/submissions/305b636b-b4f9-4287-835f-3a801c342dc3

-- Generated from ChapterWignerLittleGroup.lean — solution of BookProof.ChapterWignerLittleGroup.littleGroup_conj
import Mathlib
import Definitions.Def_ChapterWignerLittleGroup
import Theorems.Thm_BookProof_ChapterWignerLittleGroup_act_one
import Theorems.Thm_BookProof_ChapterWignerLittleGroup_act_mul
import Definitions.Def_ChapterLittleGroup
open BookProof.ChapterWignerLittleGroup



open Matrix Complex

set_option maxHeartbeats 1000000 in
theorem solution {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.det = 1) {p q : Fin 4 → ℝ}
    (h : act A (hermOfMom p) = hermOfMom q) :
    littleGroup q = (fun B => A * B * A⁻¹) '' littleGroup p := by

  have hunit : IsUnit A.det := by rw [hA]; exact isUnit_one
  have hAinv : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hunit
  have hinvA : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hunit
  have hdetinv : (A⁻¹).det = 1 := by
    rw [Matrix.det_nonsing_inv, hA]; simp
  have hcancelL : ∀ M : Matrix (Fin 2) (Fin 2) ℂ, A * (A⁻¹ * M) = M := fun M => by
    rw [← Matrix.mul_assoc, hAinv, Matrix.one_mul]
  have hactL : ∀ X : Matrix (Fin 2) (Fin 2) ℂ, act A⁻¹ (act A X) = X := fun X => by
    rw [← act_mul, hinvA, act_one]
  ext C
  constructor
  · rintro ⟨hCdet, hC⟩
    refine ⟨A⁻¹ * C * A, ⟨?_, ?_⟩, ?_⟩
    · rw [Matrix.det_mul, Matrix.det_mul, hCdet, hdetinv, hA]; ring
    · rw [act_mul, act_mul, h, hC, ← h, hactL]
    · change A * (A⁻¹ * C * A) * A⁻¹ = C
      calc A * (A⁻¹ * C * A) * A⁻¹ = A * (A⁻¹ * (C * (A * A⁻¹))) := by noncomm_ring
        _ = C := by rw [hAinv, Matrix.mul_one, hcancelL]
  · rintro ⟨B, ⟨hBdet, hB⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [Matrix.det_mul, Matrix.det_mul, hBdet, hdetinv, hA]; ring
    · rw [act_mul, act_mul, ← h, hactL, hB, h]
