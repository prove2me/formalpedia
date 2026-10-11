-- Prove2me | solution 1 for BookProof.RadialMollifier.radialBump_continuous
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:49:26.243905+00:00
-- url     : https://prove2.me/submissions/88fead3c-f278-4e08-95cc-bb8a23a24430

-- Generated from ChapterRadialMollifier.lean — solution of BookProof.RadialMollifier.radialBump_continuous
import Mathlib
import Definitions.Def_ChapterRadialMollifier
import Theorems.Thm_BookProof_RadialMollifier_radialBump_contDiff
open BookProof.RadialMollifier




open MeasureTheory Metric Set Complex intervalIntegral Real
open scoped Convolution Topology ContDiff Real

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution : Continuous radialBump := radialBump_contDiff.continuous
