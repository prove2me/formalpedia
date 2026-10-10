-- Prove2me | solution 1 for BookProof.ChapterPauliFundamental.exists_inter_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:36:29.623612+00:00
-- url     : https://prove2.me/submissions/735713f3-5d29-4c6f-a6f3-93027e167c68

-- Generated from ChapterPauliFundamental.lean — solution of BookProof.ChapterPauliFundamental.exists_inter_ne_zero
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
theorem solution : ∃ F : M4, inter A F ≠ 0 := by

  by_contra hcon
  push_neg at hcon
  -- every entry of every product `gpF A T` vanishes
  have hzero : ∀ (T : Finset (Fin 4)) (m i : Fin 4), gpF A T m i = 0 := by
    intro U m i
    -- the combination `∑_T (gpF A T) m i • (G T)ᵀ` vanishes
    have hcomb : ∑ T : Finset (Fin 4), (gpF A T m i) • (G T)ᵀ = 0 := by
      ext j n
      have h := congrFun (congrFun (hcon (Matrix.single i j (1 : ℂ))) m) n
      have hexp : ∀ T : Finset (Fin 4),
          (gpF A T * Matrix.single i j (1 : ℂ) * (G T)ᵀ) m n
            = (gpF A T m i) * ((G T)ᵀ j n) := by
        intro T
        simp [Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, mul_comm]
      simp only [inter, Matrix.sum_apply, hexp] at h
      simpa [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] using h
    -- pair with `G U` through the trace
    have h := congrArg (fun X : M4 => (X * G U).trace) hcomb
    simp only [Finset.sum_mul, Matrix.trace_sum, Matrix.smul_mul, Matrix.trace_smul,
      smul_eq_mul, Matrix.zero_mul, Matrix.trace_zero] at h
    have hTr : ∀ T : Finset (Fin 4), ((G T)ᵀ * G U).trace = if U = T then 4 else 0 := by
      intro T
      rw [Matrix.trace_mul_comm]
      exact G_traceOrth U T
    rw [Finset.sum_congr rfl (fun T _ => by rw [hTr T])] at h
    simp only [mul_ite, mul_zero] at h
    rw [Finset.sum_ite_eq Finset.univ U (fun T => gpF A T m i * 4)] at h
    simp only [Finset.mem_univ, if_true] at h
    have h4 : (4 : ℂ) ≠ 0 := by norm_num
    exact (mul_eq_zero.1 h).resolve_right h4
  have h1 := hzero ∅ 0 0
  rw [gpF_empty] at h1
  simp at h1
