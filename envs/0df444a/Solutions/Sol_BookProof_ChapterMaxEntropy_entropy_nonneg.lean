-- Prove2me | solution 1 for BookProof.ChapterMaxEntropy.entropy_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:53:39.920977+00:00
-- url     : https://prove2.me/submissions/7942fa2c-97e4-45f4-9a83-46343c14dde4

-- Generated from ChapterMaxEntropy.lean — solution of BookProof.ChapterMaxEntropy.entropy_nonneg
import Mathlib
import Definitions.Def_ChapterMaxEntropy
import Theorems.Thm_BookProof_ChapterMaxEntropy_IsProb_le_one
import Theorems.Thm_BookProof_ChapterDutchBook_Coherent_nonneg
import Definitions.Def_ChapterDutchBook
import Definitions.Def_ChapterIrreversible
open BookProof.ChapterMaxEntropy



open Real BigOperators Finset


variable {α : Type*} [Fintype α]

variable {α : Type*} [Fintype α]

set_option maxHeartbeats 1000000 in
theorem solution {p : α → ℝ} (hp : IsProb p) : 0 ≤ entropy p := by

  unfold entropy
  apply Finset.sum_nonneg
  intro i _
  exact Real.negMulLog_nonneg (hp.nonneg i) (hp.le_one i)
