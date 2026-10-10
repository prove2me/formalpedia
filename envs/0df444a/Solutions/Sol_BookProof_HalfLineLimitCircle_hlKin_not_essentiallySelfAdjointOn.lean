-- Prove2me | solution 1 for BookProof.HalfLineLimitCircle.hlKin_not_essentiallySelfAdjointOn
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:40:59.470102+00:00
-- url     : https://prove2.me/submissions/343f8ab5-78c3-478a-896f-e6e700c26895

-- Generated from ChapterHalfLineLimitCircle.lean — solution of BookProof.HalfLineLimitCircle.hlKin_not_essentiallySelfAdjointOn
import Mathlib
import Definitions.Def_ChapterHalfLineLimitCircle
import Theorems.Thm_BookProof_HalfLineLimitCircle_hlKin_not_deficiencyTrivialAt_I
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFarisLavineCore
open BookProof.HalfLineLimitCircle




open MeasureTheory Set BookProof.FarisLavine

noncomputable section

local notation "smoothTop" => ((⊤ : ℕ∞) : WithTop ℕ∞)

set_option maxHeartbeats 1000000 in
theorem solution : ¬ EssentiallySelfAdjointOn hlCore hlKin := fun h => hlKin_not_deficiencyTrivialAt_I h.1
