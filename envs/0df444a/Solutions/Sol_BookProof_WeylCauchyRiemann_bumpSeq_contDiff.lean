-- Prove2me | solution 1 for BookProof.WeylCauchyRiemann.bumpSeq_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:37:46.131831+00:00
-- url     : https://prove2.me/submissions/13670711-08c9-49ba-a11a-d81ee0b940dc

-- Generated from ChapterWeylCauchyRiemann.lean — solution of BookProof.WeylCauchyRiemann.bumpSeq_contDiff
import Mathlib
import Definitions.Def_ChapterWeylCauchyRiemann
import Definitions.Def_ChapterRadialMollifier
open BookProof.WeylCauchyRiemann




open MeasureTheory Metric Set Filter Complex BookProof.RadialMollifier
open scoped Convolution Topology ContDiff

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) : ContDiff ℝ ∞ ((bumpSeq n).normed volume) := (bumpSeq n).contDiff_normed
