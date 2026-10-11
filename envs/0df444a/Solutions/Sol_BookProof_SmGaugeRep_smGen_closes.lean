-- Prove2me | solution 1 for BookProof.SmGaugeRep.smGen_closes
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:19:10.489452+00:00
-- url     : https://prove2.me/submissions/6c22a95e-ae25-47e0-834f-7dbddfdc68a9

-- Generated from ChapterSmGaugeRepresentation.lean — solution of BookProof.SmGaugeRep.smGen_closes
import Mathlib
import Definitions.Def_ChapterSmGaugeRepresentation
import Theorems.Thm_BookProof_SmGaugeRep_smGenP_closes
import Definitions.Def_ChapterSmBrstGhost
import Definitions.Def_ChapterYangMillsSU3
open BookProof.SmGaugeRep




open Matrix Kronecker
open BookProof.YangMillsSU3 BookProof.SmBrstGhost

noncomputable section

variable {S3 : Fin 8 → Matrix (Fin 3) (Fin 3) ℂ} {f3 : Fin 8 → Fin 8 → Fin 8 → ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (hS3 : ClosesWithStructureConstants S3 f3) (y : ℝ) :
    ClosesWithStructureConstants (smGen S3 y) (smStruct f3) := by

  intro a b
  have hP := smGenP_closes hS3 y (smIdxEquiv a) (smIdxEquiv b)
  have hmap : smGen S3 y a * smGen S3 y b - smGen S3 y b * smGen S3 y a
      = toModes (smGenP S3 y (smIdxEquiv a) * smGenP S3 y (smIdxEquiv b)
        - smGenP S3 y (smIdxEquiv b) * smGenP S3 y (smIdxEquiv a)) := by
    rw [map_sub, map_mul, map_mul]
    rfl
  rw [hmap, hP, map_smul, map_sum]
  refine congrArg (fun M => Complex.I • M) ?_
  refine (Fintype.sum_equiv smIdxEquiv
    (fun c => ((smStruct f3 a b c : ℝ) : ℂ) • smGen S3 y c)
    (fun C => toModes (((sumStruct f3 (sumStruct su2Struct u1Struct) (smIdxEquiv a)
        (smIdxEquiv b) C : ℝ) : ℂ) • smGenP S3 y C))
    (fun c => by simp only [smGen, map_smul]; rfl)).symm
