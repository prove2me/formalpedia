-- Prove2me | solution 1 for BookProof.HalfLineLimitCircle.hasCompactSupport_conj
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:37:46.496127+00:00
-- url     : https://prove2.me/submissions/2dea8464-d17a-49d7-813b-c1ff4af34440

-- Generated from ChapterHalfLineLimitCircle.lean — solution of BookProof.HalfLineLimitCircle.hasCompactSupport_conj
import Mathlib
import Definitions.Def_ChapterHalfLineLimitCircle
import Definitions.Def_ChapterFarisLavine
open BookProof.HalfLineLimitCircle




open MeasureTheory Set BookProof.FarisLavine

noncomputable section

local notation "smoothTop" => ((⊤ : ℕ∞) : WithTop ℕ∞)

set_option maxHeartbeats 1000000 in
theorem solution {f : ℝ → ℂ} (hf : HasCompactSupport f) :
    HasCompactSupport fun x => (starRingEnd ℂ) (f x) := hf.comp_left (g := fun z : ℂ => (starRingEnd ℂ) z) (by simp)
