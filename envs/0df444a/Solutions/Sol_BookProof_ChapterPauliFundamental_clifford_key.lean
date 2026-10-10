-- Prove2me | solution 1 for BookProof.ChapterPauliFundamental.clifford_key
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:36:16.110958+00:00
-- url     : https://prove2.me/submissions/73961d8a-c8c6-4a2c-b67d-1b856a275925

-- Generated from ChapterPauliFundamental.lean — solution of BookProof.ChapterPauliFundamental.clifford_key
import Mathlib
import Definitions.Def_ChapterPauliFundamental
import Theorems.Thm_BookProof_ChapterPauliFundamental_gp_append
import Theorems.Thm_BookProof_ChapterPauliFundamental_cliff_sq
import Theorems.Thm_BookProof_ChapterPauliFundamental_gp_push
import Theorems.Thm_BookProof_ChapterPauliFundamental_sel_split
import Theorems.Thm_BookProof_ChapterPauliFundamental_sel_hi_mem
import Theorems.Thm_BookProof_ChapterPauliFundamental_sel_hi_insert
import Theorems.Thm_BookProof_ChapterPauliFundamental_lo_stepT
import Theorems.Thm_BookProof_ChapterPauliFundamental_sel_lo_ne
import Theorems.Thm_BookProof_ChapterPauliFundamental_sel_lo_length
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterGammaCommutant
import Definitions.Def_ChapterA3b
open BookProof.ChapterPauliFundamental



open Matrix Finset


open BookProof.ChapterA3 BookProof.ChapterGammaCommutant

variable {A : Fin 4 → M4}

set_option maxHeartbeats 1000000 in
theorem solution (hA : IsCliffordC A) (μ : Fin 4) (T : Finset (Fin 4)) :
    A μ * gpF A T = sgnT μ T • gpF A (stepT μ T) := by

  set c := (lo μ T).card with hc
  have hL : A μ * gp A (sel (lo μ T)) = ((-1 : ℂ) ^ c) • (gp A (sel (lo μ T)) * A μ) := by
    rw [hc, ← sel_lo_length μ T]; exact gp_push hA μ _ (sel_lo_ne μ T)
  have hsplit : gpF A T = gp A (sel (lo μ T)) * gp A (sel (hi μ T)) := by
    rw [gpF, sel_split μ T, gp_append]
  by_cases hμ : μ ∈ T
  · have hstep : stepT μ T = T.erase μ := if_pos hμ
    have hlo : lo μ (T.erase μ) = lo μ T := by rw [← hstep]; exact lo_stepT μ T
    have h2 : gp A (sel (hi μ T)) = A μ * gp A (sel (hi μ (T.erase μ))) := by
      rw [sel_hi_mem μ T hμ]; rfl
    have h3 : gpF A (stepT μ T)
        = gp A (sel (lo μ T)) * gp A (sel (hi μ (T.erase μ))) := by
      rw [hstep, gpF, sel_split μ (T.erase μ), gp_append, hlo]
    rw [hsplit, h2, h3, sgnT, if_pos hμ, ← mul_assoc, hL]
    rw [smul_mul_assoc, mul_assoc, ← mul_assoc (A μ) (A μ), cliff_sq hA μ]
    rw [smul_mul_assoc, Matrix.one_mul, Matrix.mul_smul, smul_smul]
  · have hstep : stepT μ T = insert μ T := if_neg hμ
    have hlo : lo μ (insert μ T) = lo μ T := by rw [← hstep]; exact lo_stepT μ T
    have h3 : gpF A (stepT μ T)
        = gp A (sel (lo μ T)) * (A μ * gp A (sel (hi μ T))) := by
      rw [hstep, gpF, sel_split μ (insert μ T), gp_append, hlo, sel_hi_insert μ T hμ]
      rfl
    rw [hsplit, h3, sgnT, if_neg hμ, ← mul_assoc, hL, mul_one]
    rw [smul_mul_assoc, mul_assoc]
