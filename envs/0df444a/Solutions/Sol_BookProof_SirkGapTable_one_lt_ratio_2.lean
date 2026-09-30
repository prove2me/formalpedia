-- Prove2me | solution 2 for BookProof.SirkGapTable.one_lt_ratio
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-29T20:05:57.218649+00:00
-- url     : https://prove2.me/submissions/9800d245-eb8b-4079-9eb4-52d8e54dace6

-- Generated from ChapterSirkGapTable.lean — solution of BookProof.SirkGapTable.one_lt_ratio
import Mathlib
import Definitions.Def_ChapterSirkGapTable
import Definitions.Def_ChapterSirkCertifiedGap
open BookProof.SirkGapTable










noncomputable section


open BookProof.SirkCertifiedGap



variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]










variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]














open Real

set_option maxHeartbeats 1000000 in
theorem solution {l1 l2 p : ℝ} (hl1 : 0 < l1) (hl : l1 < l2) (hp : 0 < p) :
    1 < (l2 / l1) ^ p := by

  have h1 : 1 < l2 / l1 := (one_lt_div hl1).2 hl
  exact (one_lt_rpow_iff (by linarith)).2 (Or.inl ⟨h1, hp⟩)
