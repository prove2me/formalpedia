-- Prove2me | solution 1 for BookProof.HalfLineLimitCircle.hlKin_neg_not_essentiallySelfAdjointOn
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T07:41:17.842267+00:00
-- url     : https://prove2.me/submissions/a52abd83-6ad6-46d4-8b23-7b9d223ea8e0

import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterHalfLineLimitCircle
import Definitions.Def_ChapterFarisLavineCore
import Theorems.Thm_BookProof_HalfLineLimitCircle_hlKin_not_deficiencyTrivialAt_I
-- Generated from ChapterHalfLineLimitCircle.lean — theorem BookProof.HalfLineLimitCircle.hlKin_neg_not_essentiallySelfAdjointOn
open BookProof.HalfLineLimitCircle



open MeasureTheory Set BookProof.FarisLavine

noncomputable section

local notation "smoothTop" => ((⊤ : ℕ∞) : WithTop ℕ∞)


theorem solution : ¬ EssentiallySelfAdjointOn hlCore (-hlKin) := by
  intro h
  apply BookProof.HalfLineLimitCircle.hlKin_not_deficiencyTrivialAt_I
  intro w hw
  apply h.2 w
  intro v
  rw [LinearMap.neg_apply, inner_neg_left, hw v]
  ring

