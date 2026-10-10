-- Prove2me | solution 1 for BookProof.LorentzOrthochronous.product_time_component
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T20:54:01.305468+00:00
-- url     : https://prove2.me/submissions/e2c2e96a-fec3-47fd-944d-233c22972249

-- Generated from ChapterLorentzOrthochronous.lean — solution of BookProof.LorentzOrthochronous.product_time_component
import Mathlib
import Definitions.Def_ChapterLorentzOrthochronous
import Definitions.Def_ChapterLorentzGroup
open BookProof.LorentzOrthochronous




open Matrix
open BookProof.LorentzGroup

set_option maxHeartbeats 1000000 in
theorem solution (a b : Matrix (Fin 4) (Fin 4) ℝ) :
    (a * b) 0 0 = a 0 0 * b 0 0 + a 0 1 * b 1 0 + a 0 2 * b 2 0 + a 0 3 * b 3 0 := by

  simp [mul_apply, Fin.sum_univ_four]
