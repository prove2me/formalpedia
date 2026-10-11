-- Prove2me | solution 1 for BookProof.ChapterA3.mgamma_commutant_iff
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T00:12:41.629987+00:00
-- url     : https://prove2.me/submissions/369fbfda-28e1-4285-bcc1-288470ec13e9

-- Generated from ChapterPauliCommutant.lean — solution of BookProof.ChapterA3.mgamma_commutant_iff
import Mathlib
import Definitions.Def_ChapterPauliCommutant
import Theorems.Thm_BookProof_ChapterA3_mgamma_commutant_scalar
import Definitions.Def_ChapterA3
open BookProof.ChapterA3



open Matrix

set_option maxHeartbeats 1000000 in
theorem solution (M : Matrix (Fin 4) (Fin 4) ℂ) :
    (∀ μ, M * mgamma μ = mgamma μ * M) ↔ ∃ c : ℂ, M = c • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by

  constructor
  · intro h; exact ⟨M 0 0, mgamma_commutant_scalar M h⟩
  · rintro ⟨c, rfl⟩ μ
    simp []
