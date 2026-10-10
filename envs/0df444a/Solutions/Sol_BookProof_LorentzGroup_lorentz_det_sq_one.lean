-- Prove2me | solution 1 for BookProof.LorentzGroup.lorentz_det_sq_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:42:56.662235+00:00
-- url     : https://prove2.me/submissions/28c8916f-cb69-4d67-b443-d410e5de77c9

-- Generated from ChapterLorentzGroup.lean — solution of BookProof.LorentzGroup.lorentz_det_sq_one
import Mathlib
import Definitions.Def_ChapterLorentzGroup
import Theorems.Thm_BookProof_LorentzGroup_eta_det
open BookProof.LorentzGroup




open Matrix

set_option maxHeartbeats 1000000 in
theorem solution {l : Matrix (Fin 4) (Fin 4) ℝ} (h : IsLorentz l) :
    l.det ^ 2 = 1 := by

      unfold IsLorentz at h;
      apply_fun Matrix.det at h; norm_num [ eta_det ] at h; linarith;
