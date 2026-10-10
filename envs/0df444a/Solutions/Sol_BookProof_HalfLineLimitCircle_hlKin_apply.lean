-- Prove2me | solution 1 for BookProof.HalfLineLimitCircle.hlKin_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:37:58.518656+00:00
-- url     : https://prove2.me/submissions/913b1163-95f6-419f-9874-af29d6e11d08

-- Generated from ChapterHalfLineLimitCircle.lean — solution of BookProof.HalfLineLimitCircle.hlKin_apply
import Mathlib
import Definitions.Def_ChapterHalfLineLimitCircle
import Definitions.Def_ChapterFarisLavine
open BookProof.HalfLineLimitCircle




open MeasureTheory Set BookProof.FarisLavine

noncomputable section

local notation "smoothTop" => ((⊤ : ℕ∞) : WithTop ℕ∞)

set_option maxHeartbeats 1000000 in
theorem solution (f : testSpace) : hlKin (hlEquiv f) = -testIncl (deriv2LM f) := by

  simp [hlKin]
