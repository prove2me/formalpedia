-- Prove2me | solution 1 for BookProof.WeylCauchyRiemann.bumpSeq_rOut_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T17:21:44.350605+00:00
-- url     : https://prove2.me/submissions/e0617e6f-c2cd-4686-a4d1-a56ddfc18989

-- Generated from ChapterWeylCauchyRiemann.lean — solution of BookProof.WeylCauchyRiemann.bumpSeq_rOut_le
import Mathlib
import Definitions.Def_ChapterWeylCauchyRiemann
import Definitions.Def_ChapterRadialMollifier
open BookProof.WeylCauchyRiemann




open MeasureTheory Metric Set Filter Complex BookProof.RadialMollifier
open scoped Convolution Topology ContDiff

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) : (bumpSeq n).rOut ≤ 2 * (bumpSeq n).rIn := by

  simp only [bumpSeq]
  rw [mul_one_div]
