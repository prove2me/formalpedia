-- Prove2me | solution 1 for BookProof.ChapterPauliFundamental.inter_intertwines
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:36:28.598005+00:00
-- url     : https://prove2.me/submissions/b82a1339-cd5c-49f3-850f-515076964e5a

-- Generated from ChapterPauliFundamental.lean — solution of BookProof.ChapterPauliFundamental.inter_intertwines
import Mathlib
import Definitions.Def_ChapterPauliFundamental
import Theorems.Thm_BookProof_ChapterPauliFundamental_stepT_involutive
import Theorems.Thm_BookProof_ChapterPauliFundamental_clifford_key
import Theorems.Thm_BookProof_ChapterPauliFundamental_G_transpose_mul
import Definitions.Def_ChapterGammaCommutant
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3b
open BookProof.ChapterPauliFundamental



open Matrix Finset


open BookProof.ChapterA3 BookProof.ChapterGammaCommutant

variable {A : Fin 4 → M4}

set_option maxHeartbeats 1000000 in
theorem solution (hA : IsCliffordC A) (F : M4) (μ : Fin 4) :
    A μ * inter A F = inter A F * mgamma μ := by

  have hleft : A μ * inter A F
      = ∑ T : Finset (Fin 4), sgnT μ T • (gpF A (stepT μ T) * F * (G T)ᵀ) := by
    rw [inter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, clifford_key hA μ T,
      Matrix.smul_mul, Matrix.smul_mul]
  have hright : inter A F * mgamma μ
      = ∑ T : Finset (Fin 4),
          sgnT μ (stepT μ T) • (gpF A T * F * (G (stepT μ T))ᵀ) := by
    rw [inter, Finset.sum_mul]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [Matrix.mul_assoc, G_transpose_mul μ T, Matrix.mul_smul, Matrix.mul_assoc]
  rw [hleft, hright]
  refine Fintype.sum_equiv (Function.Involutive.toPerm (stepT μ) (stepT_involutive μ)) _ _ ?_
  intro T
  change sgnT μ T • (gpF A (stepT μ T) * F * (G T)ᵀ)
      = sgnT μ (stepT μ (stepT μ T)) • (gpF A (stepT μ T) * F * (G (stepT μ (stepT μ T)))ᵀ)
  rw [stepT_involutive μ T]
