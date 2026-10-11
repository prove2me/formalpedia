-- Prove2me | solution 1 for BookProof.WeylCauchyRiemann.bumpSeq_hasCompactSupport
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:37:47.023669+00:00
-- url     : https://prove2.me/submissions/c0aca6be-c1d8-4de1-8a63-7af12bbe2c0e

-- Generated from ChapterWeylCauchyRiemann.lean — solution of BookProof.WeylCauchyRiemann.bumpSeq_hasCompactSupport
import Mathlib
import Definitions.Def_ChapterWeylCauchyRiemann
import Definitions.Def_ChapterRadialMollifier
open BookProof.WeylCauchyRiemann




open MeasureTheory Metric Set Filter Complex BookProof.RadialMollifier
open scoped Convolution Topology ContDiff

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) :
    HasCompactSupport ((bumpSeq n).normed volume) := (bumpSeq n).hasCompactSupport_normed
