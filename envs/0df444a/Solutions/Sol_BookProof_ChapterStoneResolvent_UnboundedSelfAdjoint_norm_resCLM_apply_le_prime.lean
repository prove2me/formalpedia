-- Prove2me | solution 1 for BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.norm_resCLM_apply_le_prime
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T01:03:41.552417+00:00
-- url     : https://prove2.me/submissions/e8201a54-4a76-401d-bb5f-44867261133a

import Definitions.Def_ChapterUnitaryTransport
import Mathlib
import Definitions.Def_ChapterStoneGroup
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterSirkTrotterKato
-- Generated from ChapterStoneGroup.lean — theorem BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.norm_resCLM_apply_le'
open BookProof.ChapterStoneResolvent
open BookProof.ChapterStoneResolvent


open scoped InnerProductSpace
open Filter Topology


open BookProof.ChapterUnitaryTransport

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]


variable (T : UnboundedSelfAdjoint H)


theorem solution {n : ℝ} (y : H) :
    ‖T.resCLM (-n) y‖ ≤ (1 / |n|) * ‖y‖ := by
  have h := T.norm_resCLM_apply_le (-n) y
  rwa [abs_neg] at h

