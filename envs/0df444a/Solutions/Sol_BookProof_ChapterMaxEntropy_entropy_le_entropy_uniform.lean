-- Prove2me | solution 1 for BookProof.ChapterMaxEntropy.entropy_le_entropy_uniform
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:55:04.508162+00:00
-- url     : https://prove2.me/submissions/0cd0b403-f0b5-4945-bb70-b56b5f52f4d0

-- Generated from ChapterMaxEntropy.lean — solution of BookProof.ChapterMaxEntropy.entropy_le_entropy_uniform
import Mathlib
import Definitions.Def_ChapterMaxEntropy
import Theorems.Thm_BookProof_ChapterMaxEntropy_entropy_le_log_card
import Theorems.Thm_BookProof_ChapterMaxEntropy_entropy_uniform
import Definitions.Def_ChapterA3n
import Definitions.Def_ChapterDutchBook
import Definitions.Def_ChapterIrreversible
open BookProof.ChapterMaxEntropy



open Real BigOperators Finset


variable {α : Type*} [Fintype α]

variable {α : Type*} [Fintype α]

set_option maxHeartbeats 1000000 in
theorem solution [Nonempty α] {p : α → ℝ} (hp : IsProb p) :
    entropy p ≤ entropy (uniform α) := by

  rw [entropy_uniform]
  exact entropy_le_log_card hp
