-- Prove2me | solution 1 for BookProof.ChapterA3.spinLie_det_exp_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:10:07.490322+00:00
-- url     : https://prove2.me/submissions/fbd77e48-8dd0-4923-adc5-e689706e79a8

-- Generated from ChapterA3f.lean — solution of BookProof.ChapterA3.spinLie_det_exp_eq_one
import Mathlib
import Definitions.Def_ChapterA3f
import Theorems.Thm_BookProof_ChapterA3_det_exp_eq_exp_trace
import Theorems.Thm_BookProof_ChapterA3_spinLie_traceless
open BookProof.ChapterA3



open Matrix NormedSpace
open scoped Norms.Operator


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {G : Matrix (Fin 4) (Fin 4) ℝ} (hG : IsSpinLie G) :
    (NormedSpace.exp G).det = 1 := by

  rw [det_exp_eq_exp_trace, spinLie_traceless hG, Real.exp_zero]
