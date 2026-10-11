-- Prove2me | solution 1 for BookProof.WeylCauchyRiemann.bumpSeq_support
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:37:45.151778+00:00
-- url     : https://prove2.me/submissions/14293238-3f44-4cde-82f7-b71ed74a4b5d

-- Generated from ChapterWeylCauchyRiemann.lean — solution of BookProof.WeylCauchyRiemann.bumpSeq_support
import Mathlib
import Definitions.Def_ChapterWeylCauchyRiemann
import Definitions.Def_ChapterRadialMollifier
open BookProof.WeylCauchyRiemann




open MeasureTheory Metric Set Filter Complex BookProof.RadialMollifier
open scoped Convolution Topology ContDiff

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) :
    Function.support ((bumpSeq n).normed volume) ⊆ ball (0 : ℂ) ((bumpSeq n).rOut) := (bumpSeq n).support_normed_eq.subset
