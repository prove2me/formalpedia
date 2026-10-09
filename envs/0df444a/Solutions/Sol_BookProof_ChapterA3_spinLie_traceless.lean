-- Prove2me | solution 1 for BookProof.ChapterA3.spinLie_traceless
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:08:54.009292+00:00
-- url     : https://prove2.me/submissions/e4a2278d-92df-441a-8dea-7513dcdd2fff

-- Generated from ChapterA3e.lean — solution of BookProof.ChapterA3.spinLie_traceless
import Mathlib
import Definitions.Def_ChapterA3e
import Theorems.Thm_BookProof_ChapterA3_spinBoost_traceless
import Theorems.Thm_BookProof_ChapterA3_spinRot_traceless
open BookProof.ChapterA3



open Matrix

set_option maxHeartbeats 1000000 in
theorem solution {G : Matrix (Fin 4) (Fin 4) ℝ} (hG : IsSpinLie G) :
    G.trace = 0 := by

  obtain ⟨b, r, rfl⟩ := hG
  rw [Matrix.trace_add, Matrix.trace_sum, Matrix.trace_sum]
  simp only [Matrix.trace_smul, spinBoost_traceless, spinRot_traceless, smul_zero,
    Finset.sum_const_zero, add_zero]
