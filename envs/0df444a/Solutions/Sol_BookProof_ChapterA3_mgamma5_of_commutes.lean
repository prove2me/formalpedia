-- Prove2me | solution 1 for BookProof.ChapterA3.mgamma5_of_commutes
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T00:12:42.643324+00:00
-- url     : https://prove2.me/submissions/8e17c2fa-f824-444f-bcb3-4383b44b62da

-- Generated from ChapterPauliCommutant.lean — solution of BookProof.ChapterA3.mgamma5_of_commutes
import Mathlib
import Definitions.Def_ChapterPauliCommutant
import Theorems.Thm_BookProof_ChapterA3_mgamma_commutant_scalar
import Definitions.Def_ChapterA3
open BookProof.ChapterA3



open Matrix

set_option maxHeartbeats 1000000 in
theorem solution (M : Matrix (Fin 4) (Fin 4) ℂ)
    (h : ∀ μ, M * mgamma μ = mgamma μ * M) :
    M * mgamma5 = mgamma5 * M := by

  rw [mgamma_commutant_scalar M h]
  simp []
