-- Prove2me | solution 1 for BookProof.ChapterPauliFundamental.G_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:36:25.143542+00:00
-- url     : https://prove2.me/submissions/7c6c64a7-fb06-474a-bacb-f58f891414ad

-- Generated from ChapterPauliFundamental.lean — solution of BookProof.ChapterPauliFundamental.G_linearIndependent
import Mathlib
import Definitions.Def_ChapterPauliFundamental
import Theorems.Thm_BookProof_ChapterPauliFundamental_G_traceOrth
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterGammaCommutant
open BookProof.ChapterPauliFundamental



open Matrix Finset


open BookProof.ChapterA3 BookProof.ChapterGammaCommutant

variable {A : Fin 4 → M4}

set_option maxHeartbeats 1000000 in
theorem solution : LinearIndependent ℂ G := by

  rw [Fintype.linearIndependent_iff]
  intro g hg U
  have h := congrArg (fun X : M4 => (X * (G U)ᵀ).trace) hg
  simp only [Finset.sum_mul, Matrix.trace_sum, zero_mul, Matrix.trace_zero,
    Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul] at h
  rw [Finset.sum_congr rfl (fun T _ => by rw [G_traceOrth T U])] at h
  simp only [mul_ite, mul_zero] at h
  rw [Finset.sum_ite_eq' Finset.univ U (fun T => g T * 4)] at h
  simp only [Finset.mem_univ, if_true] at h
  have h4 : (4 : ℂ) ≠ 0 := by norm_num
  exact (mul_eq_zero.1 h).resolve_right h4
