-- Prove2me | solution 1 for BookProof.SmGaugeRep.smGenP_closes
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:19:09.508764+00:00
-- url     : https://prove2.me/submissions/56f67f7a-47c0-4253-8cf5-e803ede1fa8d

-- Generated from ChapterSmGaugeRepresentation.lean — solution of BookProof.SmGaugeRep.smGenP_closes
import Mathlib
import Definitions.Def_ChapterSmGaugeRepresentation
import Theorems.Thm_BookProof_SmGaugeRep_su2gen_closes
import Theorems.Thm_BookProof_SmGaugeRep_sub_kronecker
import Theorems.Thm_BookProof_SmGaugeRep_kronecker_sub
import Theorems.Thm_BookProof_SmGaugeRep_sum_kronecker_left
import Theorems.Thm_BookProof_SmGaugeRep_kronecker_sum_right
import Theorems.Thm_BookProof_SmGaugeRep_smGenP_hyp_comm
import Theorems.Thm_BookProof_SmGaugeRep_smGenP_col_iso_comm
import Definitions.Def_ChapterParitySU2
import Definitions.Def_ChapterSmBrstGhost
import Definitions.Def_ChapterYangMillsSU3
open BookProof.SmGaugeRep




open Matrix Kronecker
open BookProof.YangMillsSU3 BookProof.SmBrstGhost

noncomputable section

variable {S3 : Fin 8 → Matrix (Fin 3) (Fin 3) ℂ} {f3 : Fin 8 → Fin 8 → Fin 8 → ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (hS3 : ClosesWithStructureConstants S3 f3) (y : ℝ)
    (A B : Fin 8 ⊕ (Fin 3 ⊕ Fin 1)) :
    smGenP S3 y A * smGenP S3 y B - smGenP S3 y B * smGenP S3 y A
      = Complex.I • ∑ C, ((sumStruct f3 (sumStruct su2Struct u1Struct) A B C : ℝ) : ℂ)
          • smGenP S3 y C := by

  revert A B
  have hzero : ∀ A B : Fin 8 ⊕ (Fin 3 ⊕ Fin 1),
      smGenP S3 y A * smGenP S3 y B - smGenP S3 y B * smGenP S3 y A = 0 →
      (∀ D, sumStruct f3 (sumStruct su2Struct u1Struct) A B D = 0) →
      smGenP S3 y A * smGenP S3 y B - smGenP S3 y B * smGenP S3 y A
        = Complex.I • ∑ D, ((sumStruct f3 (sumStruct su2Struct u1Struct) A B D : ℝ) : ℂ)
            • smGenP S3 y D := by
    intro A B h0 hf
    rw [h0]
    refine (smul_eq_zero_of_right _ ?_).symm
    refine Finset.sum_eq_zero fun D _ => ?_
    rw [hf D]
    simp
  intro A B
  rcases A with a | (k | u) <;> rcases B with b | (l | v)
  · -- colour / colour
    have hcomm : smGenP S3 y (Sum.inl a) * smGenP S3 y (Sum.inl b)
        - smGenP S3 y (Sum.inl b) * smGenP S3 y (Sum.inl a)
        = (S3 a * S3 b - S3 b * S3 a) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      simp only [smGenP, ← Matrix.mul_kronecker_mul, Matrix.one_mul, sub_kronecker]
    rw [hcomm, hS3 a b, Matrix.smul_kronecker, sum_kronecker_left]
    congr 1
    rw [Fintype.sum_sum_type]
    have h2 : ∑ D : Fin 3 ⊕ Fin 1,
        ((sumStruct f3 (sumStruct su2Struct u1Struct) (Sum.inl a) (Sum.inl b)
          (Sum.inr D) : ℝ) : ℂ) • smGenP S3 y (Sum.inr D) = 0 := by
      refine Finset.sum_eq_zero fun D _ => ?_
      rcases D with D | D <;> simp [sumStruct]
    rw [h2, add_zero]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.smul_kronecker]
    rfl
  · -- colour / weak
    refine hzero _ _ ?_ ?_
    · rw [sub_eq_zero]
      exact smGenP_col_iso_comm _ _
    · intro D; rcases D with D | (D | D) <;> rfl
  · -- colour / hypercharge
    refine hzero _ _ ?_ ?_
    · rw [sub_eq_zero]
      exact (smGenP_hyp_comm y _).symm
    · intro D; rcases D with D | (D | D) <;> rfl
  · -- weak / colour
    refine hzero _ _ ?_ ?_
    · rw [sub_eq_zero]
      exact (smGenP_col_iso_comm _ _).symm
    · intro D; rcases D with D | (D | D) <;> rfl
  · -- weak / weak
    have hcomm : smGenP S3 y (Sum.inr (Sum.inl k)) * smGenP S3 y (Sum.inr (Sum.inl l))
        - smGenP S3 y (Sum.inr (Sum.inl l)) * smGenP S3 y (Sum.inr (Sum.inl k))
        = (1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗ₖ (su2gen k * su2gen l - su2gen l * su2gen k) := by
      simp only [smGenP, ← Matrix.mul_kronecker_mul, Matrix.one_mul, kronecker_sub]
    rw [hcomm, su2gen_closes k l, Matrix.kronecker_smul, kronecker_sum_right]
    congr 1
    rw [Fintype.sum_sum_type]
    have h1 : ∑ D : Fin 8,
        ((sumStruct f3 (sumStruct su2Struct u1Struct) (Sum.inr (Sum.inl k))
          (Sum.inr (Sum.inl l)) (Sum.inl D) : ℝ) : ℂ) • smGenP S3 y (Sum.inl D) = 0 :=
      Finset.sum_eq_zero fun D _ => by simp [sumStruct]
    rw [h1, zero_add, Fintype.sum_sum_type]
    have h2 : ∑ D : Fin 1,
        ((sumStruct f3 (sumStruct su2Struct u1Struct) (Sum.inr (Sum.inl k))
          (Sum.inr (Sum.inl l)) (Sum.inr (Sum.inr D)) : ℝ) : ℂ)
          • smGenP S3 y (Sum.inr (Sum.inr D)) = 0 :=
      Finset.sum_eq_zero fun D _ => by simp [sumStruct]
    rw [h2, add_zero]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.kronecker_smul]
    rfl
  · -- weak / hypercharge
    refine hzero _ _ ?_ ?_
    · rw [sub_eq_zero]
      exact (smGenP_hyp_comm y _).symm
    · intro D; rcases D with D | (D | D) <;> rfl
  · -- hypercharge / colour
    refine hzero _ _ ?_ ?_
    · rw [sub_eq_zero]
      exact smGenP_hyp_comm y _
    · intro D; rcases D with D | (D | D) <;> rfl
  · -- hypercharge / weak
    refine hzero _ _ ?_ ?_
    · rw [sub_eq_zero]
      exact smGenP_hyp_comm y _
    · intro D; rcases D with D | (D | D) <;> rfl
  · -- hypercharge / hypercharge
    refine hzero _ _ ?_ ?_
    · rw [sub_eq_zero]
      exact smGenP_hyp_comm y _
    · intro D; rcases D with D | (D | D) <;> rfl
