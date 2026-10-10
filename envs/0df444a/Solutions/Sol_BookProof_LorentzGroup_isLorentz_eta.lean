-- Prove2me | solution 1 for BookProof.LorentzGroup.isLorentz_eta
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:43:30.972184+00:00
-- url     : https://prove2.me/submissions/acfd0919-4ad5-4830-8f94-b9a13d159827

-- Generated from ChapterLorentzGroup.lean — solution of BookProof.LorentzGroup.isLorentz_eta
import Mathlib
import Definitions.Def_ChapterLorentzGroup
import Theorems.Thm_BookProof_LorentzGroup_eta_transpose
import Theorems.Thm_BookProof_LorentzGroup_eta_mul_self
open BookProof.LorentzGroup




open Matrix

set_option maxHeartbeats 1000000 in
theorem solution : IsLorentz eta := by

  simp only [IsLorentz, eta_transpose];
  rw [ eta_mul_self, Matrix.one_mul ]
